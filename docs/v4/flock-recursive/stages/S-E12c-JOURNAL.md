# S-E12c (track L-circ) journal: the 4.1 node rows, continued (S-E12b §7)

Worktree `recursion.fast-submissions-flock`, HEAD `4919027`. Build tree `logs/fr-build-SE12c` (a copy of
`fr-build-SE12b`, probes `Plan4T`, `PlanM4`, `Init4`, `NodeDump4`, `Gen4T` and S-E8's `VTime`; scripts
re-pointed to `logs/S-E12c/`). Every lean/lake/probe command in a 16 GB scope with a timeout. No
sub-agents, no commits.

## 2026-10-28

- Baseline: `lake build FR` green in the new tree, 2,475 jobs (44 s, `.lake` copied).
- **Item 0, profiles** (`prof.sh`, one core (27, shared, load ≈ 9), `Elab.async=false`;
  `profile-*.log`, `prof-summary.txt`):

  | Module | wall | type checking | tactics | elaboration | peak RSS |
  |---|---|---|---|---|---|
  | `FRVIR4Mux` | 11.7 s | 0.06 s | 0.40 s | 3.37 s | 2.68 GB |
  | `FRNodeRows4` | 8.2 s | 0.11 s | 0.11 s | 0.19 s | 2.81 GB |
  | `FRNodeRows4Plan` | 12.7 s | 0.55 s | 1.19 s | 0.67 s | 2.84 GB |
  | `FRVIRCompile` | 41.5 s | 1.34 s | 11.9 s | 1.96 s | 2.77 GB |

  Imports ≈ 4 s of each.

### Item 1: can the group program at a fixed index be proved equivalent to `gen4 κ`?

Read `FRVIR`'s `exec`/`evalOp`, `FRVerifierC4` (`VnodeC`, `VsegC`, `progNode`, `progSeg`),
`FRSegTarget4.implSeg`, `FRVIRTplExt` (`tplExt`, `ImplT`, `compileT_sound`), the S-F4 op dumps
(`logs/S-F4/dump/ops-*.txt`) and S-E12b's prototype dump (`groups-p*.txt`).

`soundN` needs: rows + `imp`/`rep`/`tpl` at the selected index `ι` ⇒
`runIR (implN κ') (progNode κ' (cells κ'))` accepts, `κ' = nodeGrp ι`. The rows give, through
`compileT_sound`, a run of the **compiled** program (the group program `progNodeG`) under some
`impl` with `ImplT impl`, at exec kind `ι`. So an equivalence "group at `ι` accepts ⇒ `gen4 κ'`
accepts" is the bridge. **As built, the group programs are not equivalent to `gen4 κ'`, at four
places** (each checked against the definitions and the dumps):

1. **The finals' op counts differ per kind.** `gen4`'s finals are `finOps4 (nodeFinP κ cells)`;
   `FinP`'s `lrR`, `e2R`, `e4R`, `mB`, `nc`, `cells` are scalars, and `finPf`'s point families
   (`gPfPts`: `zSrc fi mB`, `gTailRegs … mB`, …) have `mB`-dependent lengths, so `N2`'s finals have
   21 ops fewer/other than `N4`'s (dumps: `N2` 106,221 ops, `N4`/`N8` 106,240; `L30` 106,064, `L31`
   106,072, `L32` 106,081; the constructor sequences agree up to op 102,101 and then diverge:
   `mulKF`, `addK`, `getK`, `mulK` insertions in the `mB` families). Registers are positional
   (`exec` appends), so no choice of KC tables makes one program equal, op for op, to each kind's
   at its index. `groupFinP` takes `N4`'s/`L32`'s counts, so at index `P30` the group runs `N4`'s
   finals on an `N2` proof: e.g. E2's `eqPt` over 23 coordinates where `N2`'s is over 22 (an extra
   factor `eq(x, y)` at a dummy round, not `1` in general). **Not equivalent.**
   `cells` enter `gCellsOps` as register choices (`cell.testBit v`), so `N4` and `N8` (different
   `cells4`) differ in register arguments, not only in tables.
2. **The final message's zero tail.** `finalOps4` reads `piField 0 (fo + 2^(m−25)·32) len_m`:
   offset and length depend on `m`, and `piField` has no kind table. The group's `finalOpsG` reads
   one tail per distinct `m` (2 registers for the node group, 3 for the segment group), so every
   later register is shifted against `gen4`'s. **Not op-aligned.**
3. **`hashStmt` at the index.** `evalOp (.hashStmt s)` is `stmtDigest κ`: `.N30 ↦ nodeStmtF`, else
   `leafStmtF`. `gen4` runs nodes at `.N30` and segments at `.L32`. The node group at `L32` (`N4`)
   and `P30` (`N2`) computes a **leaf** statement; the segment group at `N30` (`L31`) a **node**
   statement. Then `assertEq` against `c` checks a different relation. Also an honest witness
   cannot meet `compileT_sound`'s import hypothesis (cell = the run's value) for this register:
   H's `hashStmt` blocks compute the right digest, the run at `ι` the wrong one.
4. **The `shiftMask` template is 3.x's.** `tplExt` templates `.shiftMask t r` with
   `tplShiftMask`, and `ImplT` fixes `impl.shiftMask = NodeI.shiftMaskI` (3.x's node chain mask).
   S-E12b's prototypes instantiate it (`groups-p0`: `shiftMask 18 18`; `groups-p1`:
   `shiftMask 36 18`). `VsegC` runs `implSeg impl₀` (`shiftMask := shiftSegI`) and `VnodeC` the
   4.1 node's mask (`chainLk4`). `compileT_sound`'s run is under 3.x's mask, so at `finSh`'s
   `shiftMask` (used: `keep mk …`, `mk = vn ∨ node`) the values differ. **Not equivalent for
   every kind of both groups**, independent of 1–3. (Also: `implSeg`'s `targetS` reads
   `κ.isNode`, so at index `N30` it is the node's; fixable by a kind-blind `impl` at exec time,
   since `targetS`, `linkWAll`, `slotW` are not in `ImplT` except `slotW` (3.x's `slotWI`, which
   4.x keeps: `FRSoundness4P4aFin` uses `slotWS`).)

**What an equivalence-preserving design needs** (all inside L-circ, but large):

- (a) **A template set per revision**: `shiftMask` not templated by 3.x's (an import bound per kind,
  or a 4.1 per-kind template), i.e. `tplExt`/`ImplT`/`compileT_sound` with a filter, and the plan's
  proofs (`compMS_eq`, `compMS_T`, `slotRP_rows`, `planData*_rows`) over it. 3.x's instantiation
  must stay `rfl`-equal.
- (b) **A verified merge of the three kinds' programs** (instead of the hand-written `gen4G`):
  merge the ops of `gen4 (G ι)` position by position under per-kind register renamings
  `f_ι : ℕ → ℕ`: equal ops up to tables become one op with tables; others become per-kind copies
  with their asserts gated to their index (junk at the other indices: pure, no ask, asserts off);
  an untrusted schedule (a diff) aligns the lists. One generic theorem: if the merge's flag is
  `true`, at every index the merged run simulates `gen4 (G ι)`'s (`∀ r, rd regsG (f_ι r) =
  rd regs r`). If the flag is `false`, the slot's program is a fixed always-rejecting program, so
  `soundN` holds vacuously and the kernel never evaluates the merge. Needs `Op.mapReg` and its
  `evalOp` lemma (all ~55 constructors), the merge, the schedule, the exec simulation.
- (c) **`hashStmt` as an imported fact** (the ruling): the merge replaces it by `.input 1` and
  records the fact `stmtDigest tix (π's stmt bytes) = c` (its operand's producer is a `piField`,
  read off the op list by the merge); `imp` carries the fact, bound by H's `hashStmt` blocks.
- (d) The final tail (2) falls out of (b): the three `piField` + `assertZero` pairs become gated
  copies.
- Row cost of (b): the lists agree structurally up to op 102,101 of ≈ 106,240 (a lockstep merge
  gives tables there), so ≈ 4.1 k ops per kind are copied (`finPf`'s tail): estimated tens of
  thousands of rows per slot, not the ≈ 200 k of copying all finals (walkAB 85.5 k, phiRS 512 ×
  134, maskRows 16.4 k, rowW 16.8 k are before op 102,101).

Ruling (task): "if that is infeasible, stop and report the exact obstruction". The literal
equivalence for the existing group programs is false (1–4); an equivalent design is (a)–(d), with
(a) reaching into S-E13's plan proofs. → Reported in the RESULT; the remaining items continue where
they do not depend on it.

### Item 2: the plan (B-16, ≤ 2 s)

- Breakdown before (`planm4-a.log`, core 28, VM load ≈ 9): z0 210, z1 173, kms 134, r0 239, r1 169,
  slotRP 195 + 264, groupRP 200, pieces 38 + 40, keys 14, pats 172, prep 45, inR 86 ms; process start
  2.82 s (`plan4t-init-a.log`).
- **Layouts as constants** (`FRNodeRows4Hint`, printed by the probe `LayDump4` from `layOf`):
  `protoLay π := hintLay π`. Sound at every layout (`compileT_sound`, `slotRP_rows`); the fit is now
  checked (below). Removes both first compile passes; the key data come from the layouts' keys.
- **Region check** with each key's shared forms checked once (`shInB`): 86 → 37 ms.
- **Run patterns from prototype 0's pieces only** (S-E13's lever): 172 → 80 ms.
- After (`planm4-b.log`): kms 121, r0 196, r1 181, slotRP 191 + 216, groupRP 163, pieces 38 + 37, keys
  13, pats 80, prep 43, inR 37, ids 70 ms. **Process start 1.80 / 1.85 / 2.03 s** (`plan4t-init-b1..3`),
  import-only start (`init4`, the plan is a module-level closed term) 1.90 s; VM load ≈ 9–10.
- `evalMT4` (`plan4t-check.log`): N2 84.6, N4 89.8, N8 59.5 ms best (S-E12b: 83.3 / 83.7 / 57.5 at load
  ≈ 5); equal to the sparse sum over `nodeIRowsP` for all three kinds (the fallback's `fitB` evaluated on
  the materialised rows: the prototypes fit).

### Item 1 (part): `hfit4`, the fit by check, the activity rows

- **`ProtoFit`** (`FRNodeRows4`): each prototype's rows lie in its region below the link rows, with
  distinct indices. `nodeIRows4 κ := if ProtoFit then (slot rows ++ link rows per slot) else
  rejectRows κ` (`one·one = 0`), noncomputable (a compiled closed term would be evaluated at every
  process start). The rows per slot are now in index order (prototype rows, then the link rows at the
  region's end).
- The plan checks `ProtoFit` on its pieces: the region (`pieceInB`) and **distinct indices by
  intervals** (`ivOf`, `ivsOkB` after a merge sort by start, `ivs_nodup`, `idsOkB_spec`); `Plan4.hR :
  inR → ProtoFit ∧ lowKeys`. The fallback evaluates `fitB` (`inSlotB_iff`, `idxNodupB_iff`,
  `protoFit_iff`) on the materialised rows.
- **`hfit4 : N4c.HFit4 nodeIRows4`** (`FRNodeRows4Fit`), no evaluation of rows: `slot_mem` (indices in
  the slot's region, cells below `2^(logM+2)`: M cells below `oneCell + vslots·2^20`, L selector bits
  below `oneCell`), `slot_nodup` (`mvC` injective on the region; link rows by `zipIdx`), regions
  disjoint; the rejecting row fits.
- **Activity rows** (`actRows4`, in `linkRows4`, now 7/8 rows): `S_σ = Σ_ι s′_ι = 1` at the previous
  node's slot and each aggregate's first sub-slot; `S_σ·(1 − S_{σ−1}) = 0` at later sub-slots.
  Lemmas: `link_facts`, `selOk_of_act`, `sel_zero_of_act`, `selSum_bit`, `act_first`, `act_mono`,
  `act_profile` (under `ActK`: sub-slot `k − 1` active and `k` inactive, the pack map's tie to `k`),
  **`selA_sel`**, **`selP_sel`** (the selector parts of `NodeResid4.selA`/`selP`). `F` has
  characteristic 2, so `Σ_i S_i = k` cannot tie `k`; the tie is the boundary (`ActK`).

### Items 5, V, checks; end of pass 1

- **`FRNodeRows4Model`**: `mRowModel4` (node slot 948,182, segment slot 600,709, WOTS 5,576, link rows),
  `mRows4_le` (each slot in one region; every kind within `N_M/1.05`), `mRowModel4_eq` (N2 2,155,200;
  N4 3,356,634; N8 4,811,312), `mRows4_neg`.
- **V(N4)** (`VTime4`, S-E8's method, core 28, alternating with 3.x's `VTime`): N4 best 217.6 / 223.5 /
  213.1 ms, median 231–241 ms; 3.x N30 best 176.2 / 182.7 ms; N4 with `evalM ≡ 0` 125.5 ms. Stand-ins:
  3.x's `evalL`, `targetS`, `linkWAll`, `shiftMask`.
- Dump regenerated (`logs/S-E12c/nodedump/`, README for P2, `SHA256SUMS`).
- Checks: `lake build FR FRNodeRows4Fit FRNodeRows4Model` 2,489 jobs green; axioms 43 declarations within
  the three; source rule 276 files, 0 findings; profiles (`prof-summary-2.txt`): `FRNodeRows4Fit` 18.6 s
  wall (simp 6.85 s), the others ≤ 11.9 s.
- RESULT written; handover in its §8 (first: the decision on §1's route).
