# S-0′ journal (revision 4.0's shapes: segments, the aggregate leaf, N4/N8)

Worktree `recursion.fast-submissions-flock`, branch `v4/flock-recursive`, HEAD `a3bc63a`, pin `6d05d00`.
Build tree `logs/fr-build-S0p` (copied from `logs/fr-build-INT6`, warm; `snap.sh` with `MINE=…`).

## 2026-10-28 — reading and the constraint that shapes the track

- Read TRACK-RULES, BLUEPRINT status/§0/§0.1 (B-11 … B-17)/§2.2–2.4/§7/A.7/changes 25, PROVER.md,
  FORMAT.md, season.toml, and the modules named in the brief.
- **Constraint C1 (decides the architecture).** `Kind` (3 constructors) is case-split in 105 places
  outside S-0's modules, among them the forbidden `FRSoundnessFr*` (`Kind.m_le : κ.m ≤ 32`,
  `cases κ <;> rfl` on `mm 6 κ`, `nrP_zero`, …), `FRX*` (`FRXLeaf`, `FRXOut`) and `FRNodeRead*`.
  `items_length = 8891`, `piSize = 797904`, `chainLen = 23146` are used by the same modules. The IR's
  kind tables are `KC α = Kind → α` inside `Op`, and the finals (`FRVIRFinals*`, 3,300 lines) hard-code
  the 3.x sizes (`"S2" 28`, `18`, `32 − κ.m`, …). So adding `L31`/`N4`/`N8` to `Kind`, or changing
  `items`/`phases`/`gen` in place, breaks modules this track may not edit, and `lake build FR` must
  stay green. **Chosen:** the 4.0 shapes are an additive, kind-parametric layer in new S-0′ modules;
  the 3.x definitions stay, and bridge lemmas show the 3.x constants are instances of the parametric
  ones. The migration of `Kind`/`Op`/finals to the 4.0 kinds is S-G12′/S-E12′'s (see RESULT).

## Item 1–2 (FRShape4, FRSegment, FRAgg)

- `FRShape4`: kinds `SegKind {L31, L32}`, `NodeKind {N4, N8}`, `aggByte`; `Dims`/`Seq` counts;
  `ladderOf m` (= `ladder32`/`ladder30` by `rfl`); `phasesOf`/`itemsOf`/`fieldSizeOf`/`piSizeOf`
  with `phasesOf_seq3` (decide), `itemsOf_seq3 : itemsOf seq3 = items`, `piSizeOf_seq3`. Node
  sequence `seqN` (m* 33, Z1 20, Z3 27, S2 29, Lr 17, E2 23, E4 26, Pf 8): 9,786 items, piSize
  830,432, stream 1,585,472 = 64 · 24,773 (E4 end absorbs 64 B instead of 32 to keep the stream a
  multiple of 64, as INT-2 did for 3.x). Built in 23 s.
- `FRSegment`: `SegStmt`, `SegHolds`, `seg_sound` (= `leaf_sound` at `n`), `seg_complete`,
  `segHolds_L32` (3.x leaf = `L32` at `2^18`), `ChainedTail`/`Chained`, `segs_compose`,
  `segView`, `segC`; controls.
- `FRAgg`: `seqAll`, `runSeq_bind_some`/`runSeq_bind_of`, `VAwith`, `VA_sound`, `SegSound`,
  `VA_extract`, `VA_complete`, `VA_reject_rest`, `VA_reject_stmt`; controls. First attempt at
  the controls with `decide +kernel` through `leafStmtF` hit a kernel deterministic timeout
  after 7 min (BLAKE2s in the kernel); reworked: the statement check is split off
  (`aggChecks_eq`), the controls evaluate only byte parsing. Build 55 s.

## Item 3–4 (FRVerifier4, FRNodeLayout4, FRVIR4, dumps) and the end checks

- `FRVerifier4`: `kindOf4`, `accWith4` (`qV4`), `V4with Vseg Vnode` (A → `V_A`, N4/N8 → `Vnode`,
  segment bytes → reject, else `W`), `acc_eq4`, `V4_W_sound`, `V4_agg_extract`, `V4_encode`,
  `complete4`, controls.
- `FRNodeLayout4`: H/L/M constants for N4/N8; `hUsed_le` (119,106 ≤ 2^17; 187,364 ≤ 2^18),
  `regions_disjoint`, `mSlots_fit`, `coords_eq`; `aggChainLen 4 = 92,584` with 61 trailing bytes.
- `FRShape4`: `Sh.squeezes` now carries its challenge kind (`ChalK`), needed by the generator.
- `FRVIR4`: `genPhase4`/`skeleton4`/`gen4`/`genSeg`/`genNode`; absolute addressing (field 0).
- Dump tool `logs/fr-build-S0p/dump/IRDump4.lean` (T1's op printer). Summary: asks = items for all
  four kinds (8,891 / 9,786). `logs/S-0p/regmap.py`: the 4.0 `L32` skeleton equals 3.x's `L32`
  skeleton up to register renaming and absolute offsets (61,942 aligned ops, 0 operand
  mismatches); the 16 differing lines are the designed ones (no `kindSel`/`assertOneHot`, no
  `n = 2^18` assert, no inactive node stmt checks, the final padding check of length 0).
- `FR.lean` imports the six modules. `lake build FR` green (2,416 jobs), axioms 23/23 clean,
  source rule 0 findings. FRAgg's byte-level controls cost 11 s each in the kernel at 176-byte
  segments; shrunk to 96 bytes and the range control made generic (`aggRest_bad_n`): FRAgg kernel
  23.9 s.
- Not mine: `logs/blueprint/sizes.py`/`sizes.txt` show as modified in `git status`; untouched here.

## Redirect to revision 4.1 (coordinator, after blueprint commit 9d75d0e)

- Read changes 26, B-12, B-13. Nodes `N2` (m 31, 3 vslots), `N4` (m 32, 5), `N8` (m 32, 8), tight
  packing; segments `L30`/`L31`/`L32`; one item sequence; level-0 rows parametric.
- `FRShape4`: `SegKind` + `L30` (byte `0x50`, 3.x's `P30` byte); `NodeKind` `N2` (`0x4D`), `N4`,
  `N8` (both `m = 32`); `Seq.ell0` and `ladderOfR ell0 m` (`ladderOf = ladderOfR 6`), `Seq.lv`,
  `Seq.lvK`; `pf = m − 19 − ell0`. One sequence `seq4` (the six kinds' maximum): 3.x's with
  Lr 17, E2 23, E4 25 → 8,905 items, piSize 798,192, stream 64 · 23,168 (aligned with the 32-byte
  E4 end: no extra padding). `seqS`/`seqN` gone.
- `FRNodeLayout4` rewritten for tight packing: `hUsed` 70,955 / 117,589 / 187,540; L after H at a
  multiple of 256; M in the last `N_M/128` blocks (`N_M` 2^22 / 2^23 / 2^23); `regions_fit`.
- Kept: `FRSegment`, `FRAgg`, `hdr_A`, `L31 = 0x4B` (P2′ uses them).
- `lake build FR` green; dumps regenerated (`logs/S-0p/dump/`; the 4.0 dumps moved to
  `dump-4.0/`). `regmap.py` rewritten over GNU diff (difflib was quadratic: killed after 10 min).
  The fidelity check against 3.x stands at `seq3` (`regmap-4.0-seq3.log`: 0 mismatches); at `seq4`
  the node phases' extra rounds and the shifted caps offsets make the diff noisy (`regmap-4.1-seq4.log`).
- Axioms 23/23 clean, source rule 0 findings; profiles in `prof-*.log`.
