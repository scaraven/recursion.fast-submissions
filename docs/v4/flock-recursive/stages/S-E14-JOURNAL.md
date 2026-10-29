# S-E14 (track L-circ): JOURNAL — the replay `R` (S-N2's `Gap4`, item 7: the ten replay registers)

Base: HEAD `d7bb21e` (after S-E13b, S-I). Build tree `logs/fr-build-SE14`: a copy of
`logs/fr-build-SE13b` (against `logs/org20`); `snap.sh` snapshots HEAD and links this track's modules
(`MINE.txt`). Logs in `logs/S-E14/`. 16G scope and `timeout` on every lake/lean command. No
sub-agents, no commits. S-E13a (pack map, `FRNodeRows4*` fold) runs in parallel: this track writes
only new modules `FRNodeRows4Rep*` and edits no existing module.

## 0. Allocations (written first, for S-E13a and the orchestrator)

**Rows.** Per slot region `σ` (M-relative rows `[σ·2^20, (σ+1)·2^20)`):

| Rows (relative to the region) | Owner |
|---|---|
| `[0, 730,493)` prototype 0 / `[0, 725,885)` prototype 1 (measured, `logs/S-E13a/nodedump4-run.log`) | the compiled prototypes |
| **`[753,664, 1,015,808)` = `[23·2^15, 31·2^15)`, 262,144 rows: the replay rows `R` of the slot's own ops** | **S-E14** |
| `[1,015,808, 2^20)` the link region (`2^15`) | S-E12c, S-E13a (pack), S-E13b (WOTS, `aggPad`) |

The gap `[730,493, 753,664)` (23,171 rows) is left free so that a prototype that grows by up to 3 %
still fits under `R` (`ProtoFit` would fail otherwise; the rejecting row keeps it sound).

**The node child's `evalM` replay** (§1.6) does not fit a slot region next to the rest (§1.7). It
gets a **spare region**: `N2` region 3 (`N2` has 3 slots in `2^22 = 4` regions), `N4` region 5
(5 slots in 8 regions). `N8` has no previous node, so no `evalM` replay.

**Cells.** Per slot region, the slot-relative cells **`[2^19, 2^20)`** (524,288 cells). The prototypes
use relative cells `< 190,584` (prototype 0: 4 … 189,997; prototype 1: 4 … 190,583); S-E13a's pack
rows add no cells; S-E13b's new cells are L cells. The spare region's cells are all `R`'s.

## 1. Design note (item 1)

### 1.1 What the ten registers are

The census (S-N2 §2, `logs/S-E12f/nodedump/proto-p{0,1}.txt`) has **one op per name, six ops per
prototype**; `evalM` and `evalL` each write three registers (`A`, `B`, `C`):

| Op (prototype 0 / 1) | Line in `proto-p0` / `-p1` | Operands → result |
|---|---|---|
| `targetS` | 184 / 276 | `r45 → r178` / `r138 → r271` (`af 64`) |
| `shiftTarget` | 66502 / 66595 | `τ r57805, θ r57806, bnd r57804, κ_s r834 → r57807` / `r57899 r57900 r57898 r927 → r57901` (`f`) |
| `linkWAll` | 66524 / 66617 | `tt r57828, rr r57829 → r57830` / `r57922 r57923 → r57924` (`af 8`) |
| `evalM` | 66596 / 66689 | `r_E2 r57884, r′ r57897 → r57898 r57899 r57900` / `r57978 r57991 → r57992…4` (3 × `f`) |
| `evalL` | 66601 / 66694 | `r_Lr r57870, r′ r57897 → r57905…7` / `r57964 r57991 → r57999…r58001` (3 × `f`) |
| `rsWeight` | 102433 / 102656 | `r″, pts (per kind), κ, β, act, ρ → r93607` / `→ r93831` (`k`) |

The compiler makes each of them an **import** (`FRVIRCompile.opOut`: `imports cs [...]`: fresh typed
cells, `imp := true`). The ops the slot runs are `implP` (S-N2): prototype 0 at index `ι` runs
`(implN4F base (nodeAt ι)).fixK .N30`, prototype 1 runs `(implSeg impl₀).fixK .L32` at every index.

**Operands.** Every operand is an M register of the same slot: a point the program computed from
squeeze answers (`chF`/`chK`, `packF`/`packFK`) or a constant. None is a proof field or a trace
cell. Where the operand is a `packFK` (kind-muxed: the kinds' points differ in length or in a
padded coordinate) its cells at the run's kind are `CS.slotK a ι` (per-kind slots, S-E12f), so a
replay template is a **kind mux** (`kmuxT`'s pattern: one sub-template per selector index, outputs
`Σ_ι s_ι · out_ι`), unless the op's value does not depend on the kind.

### 1.2 The soundness mechanism (needed by every op)

`compileTF4_soundAt` (`compileX_soundK`) takes **every** import as a hypothesis at the final run
(`hi : ∀ i ∈ imp, RepS w (slot i) (rd s.regs i)`), and proves the representation of every other
register from it. A replay row can only say `cell(out) = f(cells(args))`. To turn it into
`RepS w (slot out) (f (rd s.regs args))` one needs `RepS` of the operands **at the point where the op
is compiled**, i.e. inside the induction. So the discharge is a **staged compile soundness**:
`compileFromX_soundR`, `compileFromX_soundK`'s induction with the imports of *covered* ops
discharged by their replay rows, given the invariant `InvK` at that op (this stage builds it,
`FRNodeRows4Rep`). The replay rows are defined over the compile's trail (state, op), so no
definition or proof evaluates the 106 k-op program.

### 1.3 Per op, prototype 1 (segment slots; `ι ∈ {L30, L31, L32}`, every op read at `L32`)

| Op | Spec at `L32` | Rows | Notes |
|---|---|---|---|
| `linkWAll` | `Array.replicate 8 0` (`implC`: a leaf kind's `linkWAll` is `0^8`) | **8**: `one · out_j = 0` | no operand; built here |
| `targetS` | `targetSSegI r = targetSLeafI r · segRangeI r` | `eqTable(zLo r)` 255 products; the 64 outputs of `targetSLeafI` are **linear** in the table (`chainTab` constants); `segRangeI` a dyadic range sum over the 18 block coordinates (≈ 100); 64 products: **≈ 500** | operand unmuxed (`segPtOp`: one length for the group) |
| `shiftTarget` | `shiftTargetI κs τ θ bnd` | `Eθ` (10 coordinates) 1,023 products + 1,023 linear; `digestMle` needs the 256 bits of each digest (`digBit`, not F-linear): 2 × (256 Boolean rows + 2 pack rows + 256 products); `eq(τ, last)` 35; **≈ 3.1 k** | `bnd`'s digests are the statement's (`s`, `h`), from proof fields |
| `rsWeight` | `rsWeightF` with `act = false` (no kind factor) | A.11: **≈ 45.6 k** (4 claims; `r_v^{2^k}` squarings, `eq(r^{2^k}, ρ)` K products) | operand `pts` per kind (`{L,P,N}` lists): kind mux on the claims' points |
| `evalM`, `evalL` | `impl₀.evalM` = 3.x's `evalMT pl` (the 3.x node's matrices) | **not replayable** (meaningless here) | **dead**: their only use is `assertEq … {L:false, P:false, N:false}` (proto-p1 line 66703). See §1.8 |

**Prototype 1 total: ≈ 49 k rows** per segment slot, against 289,923 free rows below the link
region (2^20 − 2^15 − 725,885).

### 1.4 Per op, prototype 0 (the previous node; `ν = nodeAt ι ∈ {N4, N2, N8}`)

| Op | Spec | Rows (per kind → muxed) | Notes |
|---|---|---|---|
| `shiftTarget` | `shiftTargetI` (base `implC`, kind-free) | `bnd` is **constant** here (`r57801 r57802 …`: `h0`'s zero halves and `1`s), so both `digestMle` are 256-term **linear** rows (no bits); `Eθ` 2,046; `eq(τ, last)` per kind (τ's coordinate 17 is `0` at `P`, i.e. `N2`): 3 × 35 + 3 mux: **≈ 2.2 k** | |
| `targetS` | `targetSNode4S ν` (computed form `FRNodeTarget4C`: interval classes `Gc4`, `clsW`, `ctrG`, `finG`, `stepG`) | A.11's node template ≈ 16 k per kind; the eq tables over `zLo r` and the block coordinates are shared, the kinds' interval sums are not: **≈ 24 k** | `nb` = 17/18 coordinates (`N2`/`N4`, `N8`) |
| `linkWAll` | `linkWAll4I ν` (8 WOTS link families, `srcB4`/`mirB4`) | ≈ 15 k per kind (A.11, S-CN §7: `6 n_f + 24 len_f` per family); shared eq tables: **≈ 35 k** | |
| `rsWeight` | `rsWeightF4`/`S4 ν` (claim 2's kind factor, `FRKindWeight4`) | claims 45.6 k (shared) + the kind factor 68.5 k (its Frobenius chains of `β` shared, the kinds' interval range sums ≈ 10 k each): **≈ 135 k** | |
| `evalL` | `evalL4I ν`: `Σ_σ eq(r4_hi, hb+σ) Σ_{j<nJ} eq(rL, σ nJ + j) eq(r4_lo, 299 + j)` | direct (tables of `2^logL` and `2^14`, `vslots · 8,220` products): ≈ 125 k per kind — **too many**. The closed form: `Σ_{j<n} eq(a, A + j) eq(b, B + j)` over a dyadic piece is a carry automaton in `O(log²)` products; `[0, 8,220)` is ≤ 14 pieces: ≈ 3–6 k per kind, **≈ 15–25 k muxed** | a new closed form and its proof |
| `evalM` | `evalMT4 planOf4 ν` = the MLE of `nodeIRows4 ν` (`evalMT4_eq`) | **`R` proper**: 240 k with S-E12b §4's levers (sparse-skeleton templating, instance AP: not built), ≈ 500 k without | the fixed point, §1.6 |

**Prototype 0 without `evalM`: ≈ 221 k rows**, against 285,315 free rows below the link region
(2^20 − 2^15 − 730,493): fits, 1.29×.

### 1.5 What `V` must evaluate (the parent's `evalM`)

`R`'s rows are part of `nodeIRows4`, so the parent's `evalMT4` must evaluate their MLE, and the
child's `evalM` spec (`evalMS4 ν`) includes the child's own `R`.
- **The per-slot templates** (§1.3–1.4) are slot-symmetric: every slot of a prototype has the same
  rows at the same relative cells, so they belong **in the prototype copy** (`copy_val`: evaluated
  once per prototype). As templates (the `tpl_mle` classes: local, shared, the eq-tree/shift closed
  forms) they cost `O(|tpl|)` per key once: prototype 0 ≈ 221 k rows → the large keys are the
  squaring chains and eq trees (closed forms `O(log)`), estimated **+5–10 ms VM**. As plain sparse
  rows (≈ 3 entries per row, ≈ 0.8 M products) they would cost ≈ +30 ms VM: too much against the
  margin (V(N4) 184–199 ms VM best today, `logs/S-E13a/vtime4-*`; cap 206 ms on the 7763 ≈ 245 ms VM
  at the measured 1.19).
- **The node child's `evalM` replay** (§1.6), in the spare region: u-rows sharing `Ĉ(τ_lo, σ_lo)`
  with the evaluation the parent does anyway, v-rows/sums `O(log)`: **+≈ 7 ms VM** (A.11). Not a
  copy: one instance per node.
- **`evalL` of the parent is unchanged** (`lRows4` is frozen): `R` adds M rows only.

Projected V(N4) after `R`: 199 + 10 + 7 ≈ **216 ms VM best ≈ 182 ms on the 7763** (1.13×), only if
every template has a closed-form MLE. **The fixed point is cut** iff every `R` row with a constant
coefficient is a linear row over regularly addressed cells and every product multiplies regularly
addressed cells (§4.4's rule), i.e. the closed form of `MLE(R)` is in `R`'s own rows.

### 1.6 `evalM` (`R` proper) and the fixed point

`R` must compute `MLE(nodeIRows4 ν)(r_E2, r′)` for the child's kind (muxed over `N2`, `N4`, `N8`),
**including the child's `R`**:
- the two prototypes' low-coordinate MLEs `MLE_lo(p)(τ_lo, σ_lo)` (the same two structures for every
  kind: S-E12b §4), then each kind's slot factors (selector-linear closed forms);
- the child's link region: S-E12c's link rows, S-E13a's 2 × 8,906 pack rows and S-E13b's
  7,992–8,680 WOTS/`aggPad` rows — **irregular H cells**: one product per entry with the eq tables
  over the blocks (≈ 2 × 18 k + 2 × 26 k products per kind: **≈ 90 k**, a cost the 240 k estimate
  did not have);
- the child's `R` (its closed form; the cut).

Rows: **≈ 240 k (levers) + 90 k (link region) ≈ 330 k**, ≈ 590 k without the levers.

### 1.7 Fit against `N_M`, and the verdict

| Region | Free rows | `R` (this note) | Fits |
|---|---|---|---|
| prototype 0 slot, without `evalM` | 285,315 | ≈ 221 k | yes (1.29×) |
| prototype 0 slot, with `evalM` | 285,315 | ≈ 221 k + 330–590 k | **no** |
| prototype 1 slot | 289,923 | ≈ 49 k | yes (5.9×) |
| a spare region (`N2` 3, `N4` 5) for `evalM` | 1,015,808 | 330–590 k | yes (1.7–3.1×) |

- **`N_M` per kind** (rows used, `N_M/1.05`): `N2` = 3 slots + spare ≈ 3 × 1.0 M + 0.6 M ≈ 3.6 M of
  3.99 M (**1.11×**, tight; ≈ 3.35 M with the levers); `N4` ≈ 5.6 M of 7.99 M; `N8` ≈ 8 × 0.77 M =
  6.2 M of 7.99 M.
- **`FRNodeRows4Model` is stale**: `protoRowsN = 551,805` is S-E12b's; the prototypes occupy 730,493
  / 725,885 rows since S-E12f. With the measured figure the model's previous-node slot is
  1,126,870 rows (> 2^20 − 2^15): `mRows4_le` holds only on the stale constant. (S-E13a owns the
  model; reported in the RESULT.)
- **Verdict.** The five ops other than `evalM` fit their slot regions and V (with templated MLEs).
  **`evalM`'s replay does not fit the previous node's slot region** with the other ops; it fits only
  in a spare region (`N2`, `N4`), and its V cost and fixed-point cut depend on S-E12b §4's levers,
  which are not built. The segment slots' `evalM`/`evalL` cannot be replayed (dead ops, §1.8).

### 1.8 The segment's dead `evalM`/`evalL`

In prototype 1 the six registers of `evalM`/`evalL` feed only `assertEq r58009 r2339
{L:false, P:false, N:false}`. Under `implSeg impl₀` their values are 3.x's node matrices'
MLEs, which no segment row can compute. Two remedies (not this track's modules):
- (a) **the generator** (`FRVIR4Mux`/`gen` owner): emit no `evalM`/`evalL` (and their gated assert)
  for the segment group — the segment verifier's acceptance does not read them;
- (b) a **non-interference lemma**: `exec` under two `OpImpl`s that differ only in `evalM`/`evalL`
  accepts alike when every use of their results is a disabled assert (needs a dataflow fact about
  `progSegG`, proved on the generator, never by evaluation).

Until then `SlotImp`'s imports of a segment slot keep these six registers.

### 1.9 The prover (P2)

Every `R` row's cells are the op's intermediate values (eq-table entries, bits of the digests,
products, the squaring chains): P2 computes them from the run it already has. The rows are a
function of the final compile state and the op list (one pass over the ops, no compile): the plan
(≤ 2 s at process start) gains one pass over 106 k ops (≈ ms).

### 1.10 V re-priced at S-E13a's measured costs (orchestrator's note, 2026-10-29)

S-E13a measured **0.6 µs per irregular row** in `evalMT4` and **0.2 µs per F product** (VM); its
≈ 26 k link rows per node cost V(N4) ≈ +30 ms. Priced that way, `R` as plain rows is out of reach:

| Op (rows) | as irregular rows | closed form available? |
|---|---|---|
| segment `linkWAll` (8 per slot) | 8 × 0.6 µs × ≤ 8 slots < 0.05 ms | not needed (built) |
| segment `targetS` (≈ 500) | 0.3 ms per slot | yes: `eqTable` is a tree template; the 64 `chainTab` rows are one constant matrix in `𝒞` (its `Ĉ` once, ≈ 16 k products ≈ 3 ms, shared by every segment slot) |
| `shiftTarget` (2.2–3.1 k) | 1.3–1.9 ms per slot | yes in principle (eq tree, strided Boolean rows, strided products); not written |
| segment `rsWeight` (45.6 k) | 27 ms per slot | **3.x's `tplRsWeight` key exists** (A.11 closed form) but `keys41` drops it: 4.1's `rsWeight` is `rsWeightF4`/`S4`; the claims part is reusable, per prototype once via the copy |
| node `rsWeight` kind factor (68.5 k + kinds) | 41 ms | **no**: `FRKindWeight4`'s Frobenius chains and range sums have no template |
| node `targetS` (≈ 24 k), `linkWAll` (≈ 35 k) | 14 ms, 21 ms | **no** template at the 4.1 layout (3.x's `targetSNode`/`linkW` estimates only) |
| node `evalL` (15–25 k) | 9–15 ms | **no**: the carry-automaton closed form is not written |
| node `evalM` (`R` proper, 330–590 k) | 200–350 ms | **no**: S-E12b §4's levers (sparse-skeleton templating, instance AP) are not built; S-E6 §4's fixed-point blocker stands |

**Stop-and-report (per the note):** of the ten registers only the segment `linkWAll` (built) and,
with new templates, the segment `targetS`/`shiftTarget` have a closed form within reach. The
previous node's six ops and the segment `rsWeight` need templates that do not exist; `evalM` needs
the levers. I build the mechanism and the one op that needs no template, and stop there.

**The pack map.** Every operand of a replay op is an M register the program computed (from squeeze
answers via `chF`/`chK`, `packF`/`packFK`) or a constant (§1.1). The staged soundness takes the
remaining imports — the squeeze answers and every other pack-map class — as hypotheses on their
cells (`impRP`: the import registers the templates do not cover), so `R` does not depend on the
pack map being built: `SlotImpR` is exactly that `hPack`-style interface.

## 2. Log

1. Build tree `logs/fr-build-SE14` (copy of `fr-build-SE13b`), `prof.sh` writes to `logs/S-E14/`.
2. **`FRNodeRows4Rep`**: `RT`, `RTOk`, `repRowsX`, `impRX` (trail-defined), `impRX_sub`,
   `impRX_none`, **`compileFromX_soundR`** (a copy of `compileFromX_soundK`'s induction; only the
   import step changes: a covered op's outputs come from `RTOk` at the aligned state with `InvK`, an
   ask cannot be covered), **`compileX_soundR`**; at the node `Xof`, `repRowsP`, `impRP`,
   `SlotRunR`, `SlotImpR`, `RepHolds`, `RepOk`, **`slotImp_of_rep`**, `slotImpR_of_imp`, `repBase`,
   `repIRows4`, `mem_zipIdx_map`, **`repHolds_of`**, **`gap4Imp_of_rep`**.
   - Kernel trap met once: `repHolds_of` timed out at `whnf` (200 k heartbeats) when an ascribed
     type `(rowMapC F r).Holds w` was unified against `hE`'s instance; `dsimp only at h3` then `rw`
     fixed it, and `generalize repRowsP … = l` keeps the program's rows opaque.
3. **`FRNodeRows4RepS`**: `zeroRows`, `isLinkW`, `rtLinkSeg`, `rtSeg`, `LinkZero`,
   `linkZero_implC` (`rfl`), `rej_not`, `zeroRows_sound`, **`rtLinkSeg_ok`**, **`repOk_rtSeg`**.
4. **`FRNodeRows4RepCtrl`**: the controls (`decide` on one-op programs only).
5. Checks: `lake build FR FRNodeRows4Rep FRNodeRows4RepS FRNodeRows4RepCtrl` green (2,569 jobs);
   axioms (18 declarations, ⊆ {propext, Classical.choice, Quot.sound}); source rule 357 files, 0
   findings; sequential profiles: type checking 0.16 / 0.08–0.17 / 0.04 s.
