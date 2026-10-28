# INT-7 RESULT: R-4's minors on the revision 4.1 verifier layer (`FR.Rev4`)

Base: HEAD `633ab78`. Build tree `logs/fr-build-INT7` (scripts from `fr-build-INT6`, `.lake` copied
from `fr-build-SG12`, `logs/org20`, `MINE` = the seven modules below). Logs: `logs/INT-7/`. Every
`lake`/`lean` command ran in the 16G scope under `timeout`. No sub-agents. Nothing committed.

The majors R-4-M1 and M2 (`SegSoundLog`, `VA_extract_log`) are not part of this item list. S-G12′ is
putting them in `FRSoundness4Agg` (in progress, not mine). That module compiles against this layer:
`logs/INT-7/sg12-agg-check.log`, 0 errors.

## What changed (code lines from `loc.py`: HEAD → now)

| Module | code | Change |
|---|---|---|
| `FRAgg` | 294 → 388 | m5, m4 (queries, `V_A` negatives), m1 (`pubStart`), m6, golf of the controls |
| `FRVerifier4` | 135 → 170 | m2 (`childOk4`), m4 (`V4_queries_le`, `ks_queries4`), docs (R-4 Q3, revision 4.1) |
| `FRNodeLayout4` | 45 → 52 | m1 (`aggSegs` → `maxK`), m4 (`lSlots_fit`), m2 (`aggChainLen_k3`, `k ∈ {2, 3, 4}`) |
| `FRSegment` | 81 → 77 | m1: `pubStart` and `Chained` removed |
| `FRShape4`, `FRVIR4`, `FRVerifierC4` | 199, 133, 45 (unchanged) | docstrings only (m3, m6, m2) |

**m2 (the verifier side).** `childOk4 κ π` holds when an aggregate child (`'A'`) has
`k ≤ κ.maxK` (`N2`: 2; `N4`/`N8`: 4). Other children are unaffected.
- **Why it is not inside `V4with`/`VnodeC`.**
  - `V4with` never sees a SNARK node's children: its node branch is `Vnode κ vk c π`, and the
    node's proof does not carry the child proofs.
  - Its only child dispatch is the `W` branch, where no `N2` is involved.
  - So the check is stated as the predicate the node circuit enforces (S-E's row) and S-G12′ uses
    as a truth. `VnodeC`'s docstring says so.
- **What is proved about it:**
  - `childOk4_chain`: a child that passes has `aggChainLen k ≤ aggChainLen κ.maxK`, so it fits H
    (`aggChainLen_le`).
  - `childOk4_of_accept`: for `maxK = 4` every proof `V4with` accepts passes it, so the check
    binds only `N2`.
- **Controls** (`childOk4_ctrl`):
  - `N2`: `k = 2` passes, `k = 3` fails;
  - `N4`: `k = 3` passes;
  - a `W` proof passes.

**m5.** `VAwith`'s parse guard now also requires `bytesAt π 2 6 = Vector.replicate 6 0`. `VA_pad`
proves that an accepting run implies it. The byte layout is unchanged.

**m4.**
- `seqAll_queries_le`, then `VA_queries_le` (`≤ 4 · qS`), then `V4_queries_le` (`≤ qV4`, given
  `4 · qS ≤ qV4` and node programs `≤ qV4`), then `ks_queries4`. The last is exactly `KS`'s
  first conjunct for a submission with `S.V = V4with …` and `S.qV = qV4`.
- The per-program bounds (`qS = 8,905`) belong to S-G. `traces_le_qV` gives `4 · 8,905 ≤ qV4`.
- `lSlots_fit` and `lSlots_N8_full` are R-4's probe lemmas, adopted.

**m1.**
- I grepped the worktree (including the untracked and modified files), `prover/`, and the
  `fr-build-SG12`/`fr-build-SE13` sources. Nothing used `pubStart`, `Chained` or
  `NodeKind.aggSegs`.
- Removed: `SegStmt.pubStart`, `Chained`, and the `Bool` argument of `SegView.stmt`.
- `NodeKind.aggSegs` was renamed `NodeKind.maxK` (same body) and is now used by `childOk4`. This
  removes the clash with `Rev4.aggSegs`.

**m6.** These docstrings are fixed:
- `itemsOf_seq3`, `piSizeOf_seq3`, `fieldOffs` (they describe `seq3`, not 4.1's segments);
- `FRShape4`'s header (revision 4.1, one sequence);
- `ladder_sq_sib` (`m` 31/30);
- `FRAgg`'s header: `VA_reject_stmt`, and "`seq4` item sequence (8,905)";
- `segs_compose_ctrl` (`ChainedTail`).

**m3.** Docstrings only (lever 5 declined). These now say that `ell0 = 6` is the ruling and that
`colBytes`, `finalOps4` and `seqOf` hard-code 6:
- `FRShape4`'s header and `Seq.ell0`;
- `FRVIR4`'s header and `finalOps4`.

## Statement changes (for S-G12′)

| Declaration | Change |
|---|---|
| `VAwith` | **meaning**: also rejects (no query) unless `hdrA` bytes 2–7 are zero |
| `VA_complete` | **new hypothesis** `hpad : bytesAt π 2 6 = Vector.replicate 6 0` |
| `SegStmt` | field `pubStart` removed |
| `SegView.stmt` | `(v : SegView) : SegStmt` (no `Bool` argument) |
| `SegKSOn` | conclusion `∃ z, SegHolds v.kind v.stmt z` (was `∃ b z, … (v.stmt b) …`) |
| `ChainedTail` | the `pubStart = true` conjunct removed |
| `seg_complete`, `seg_wrong_end`, `seg_ctrl_pos`, `seg_bad_n`, `segHolds_L32` | the `Bool`/`false` argument removed |
| `Chained`, `NodeKind.aggSegs` | removed (`NodeKind.maxK` replaces the latter) |
| new | `VA_k_range`, `VA_pad`, `seqAll_queries_le`, `VA_queries_le`, `V4_queries_le`, `ks_queries4`, `childOk4`, `childOk4_chain`, `childOk4_of_accept`, `NodeKind.maxK`, `maxK_eq`, `aggChainLen_le`, `aggChainLen_k3`, `lSlots_fit`, `lSlots_N8_full`, `aggSegs_flat`, `ctrlA_mapM`, `ctrlAx`, `ctrlViews5` |

Every other statement is unchanged: `VA_sound`, `VA_extract`, `VA_extract_on`, `VA_reject_*`,
`aggChecks`, `aggWit`, `V4with`'s and `kindOf4`'s definitions, and every `FRVerifier4` and
`FRVerifierC4` theorem.

The check on bytes 2–7 sits in `VAwith`'s outer `if` condition. Every proof that does
`split at h` on `VAwith` therefore goes through unchanged: `VA_sound` here, `VA_sound_log` in
S-G12′'s `FRSoundness4Agg`. The check changes the meaning of `V4with`'s `A` branch only.

The other re-proofs:
- **`acc_eq4` and `acc_eqC4`** need no change: they unfold `Submission.acc` against `accWith4`
  and never look inside `V4with`.
- **`complete4`** needs no change: it runs only the `W` path (`V4_encode`).
- **`ctrlA_pos`** passes the new `hpad` hypothesis (`decide +kernel`; `aggHdr` writes zeros).

## Controls (new; each is kernel-checked)

All of these are rejected:
- `ctrlA_bad_pad`: `ctrlA_pos`'s bytes with byte 2 set to `1`.
- `ctrlA_bad_end`: `e_k ≠ e` fails `aggRest`, and the same views with `e = e_k` pass.
- `ctrlA_k0`: a 48-byte `hdrA` with `k = 0`, which passes the size and padding checks.
- `ctrlA_k5`: five valid chained views fail `aggRest`, and their first four pass.
- `ctrlA_cap_kind`: an `L31` view of `2^17 + 1` steps fails, and the same view as `L32` passes.

## Times (sequential elaboration, `-DElab.async=false --profile`)

- **`FRAgg`:** kernel 26.9 s → **7.4 s** (`logs/INT-7/prof-FRAgg-0.log` → `prof-FRAgg-1.log`).
  - Each of the three byte-level controls spent about 8 s evaluating `aggSegs` (`ByteArray.extract`)
    in the kernel.
  - They now share `aggSegs_flat`, a lemma that `aggSegs` of `hdr ‖ segs.flatten` is `segs`, and
    then `decide` only the two `segView`s. Their statements are unchanged.
- **`FRNodeLayout4`:** kernel 7.75 s → 10.7 s. `aggChainLen_k3` adds about 3 s, and `simp` does not
  make it cheaper.
- **`FRVerifier4`:** 0.07 s. **`FRSegment`:** 0.02 s.
- **`lake build FR`:** green, 2,419 jobs (`logs/INT-7/build-FR.log`).

## Checks

- **Axioms:** 40 declarations (`logs/INT-7/axioms.log`), within `propext`, `Classical.choice` and
  `Quot.sound`.
- **Source rule:** `python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive` gives
  198 files, 0 findings.
- **Dumps:** none. No program's ops changed: `genSeg`/`genNode` are untouched, and `V_A` is not an
  IR program.

## For P2‴

`V_A` now checks `hdr_A` bytes 2–7 = 0, at the same offsets. `prover/agg.rs` already writes zeros
there and checks them (l. 80). Nothing to change.

## Open points

- **S-E (L-circ).**
  - The `N2` circuit must enforce `childOk4 .N2` on its aggregate child.
  - Every node circuit needs the `k`-gated padding, counter and final block for `k ∈ {2, 3, 4}`
    (R-4-m2).
- **S-G12′.**
  - `ks_queries4` needs per-program query bounds for `VsegC`/`VnodeC` (`qS = 8,905`).
  - `childOk4` is a truth of `N2`'s node soundness.
- **Orchestrator.** B-12 still describes the gated `pubStart` row (R-4-m7). The Lean side now
  matches I-2.
