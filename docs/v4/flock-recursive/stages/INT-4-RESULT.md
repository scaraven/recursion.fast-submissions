# INT-4 RESULT: the `finZ` c-claim; revision 3.15's 18-coordinate `τ` (2026-10-28)

HEAD `b239c92` (`3817fe4` by the end: one queue commit, no Lean change). Build tree
`logs/fr-build-INT4` (`snap.sh`: HEAD's sources, this pass's five modules symlinked to the
worktree). Logs in `logs/INT-4/`. Journal: `INT-4-JOURNAL.md`. Every lean/lake command ran in the
16G scope with a `timeout`. Nothing is committed.

**State: `lake build FR` is green, 2,379 jobs** (`logs/INT-4/build-FR-2.log`). HEAD alone was green
in the same tree (`build-head.log`, 2,379 jobs). No S-G, L-circ, `FRX*` or `FRNodeRead*` module
needed a repair, and `FR.lean` is unchanged.

## 1. What changed, by module (code lines from `loc.py`, HEAD → INT-4)

| Module (owner) | Change | Code |
|---|---|---|
| `FRVIRFinals` (S-0) | **`finZ`** asserts `P^z*(λ) = α_Z`; **`relZ`**, `flag_finZ` restated, `relZ_iff`, controls `finZ_rejects`/`finZ_accepts`; **`bndOps`** (a `1` register, `bnd` of 22), **`padB`**, **`finSh`** (`τ`, `r_blk` of 18, `E₀`'s point `0^18`, `b = b₀ + 8`), **`relSh`** (same), `flag_finSh` proof repair | 308 → 346 |
| `FRVIR` (S-0) | `Meets`: `shiftTarget`'s precondition `bnd.size = 4` → `22`; docstrings of `Op.shiftTarget`, `OpImpl.shiftTarget` | 586 → 586 |
| `FRShift` (S-C) | **`padZ`**, **`eq_pad_zero`**, `shiftPair_zeros`, **`shiftPair_pad`**, **`shiftTargetAt`** (the target at a given last block), **`shiftTarget_pad`** | 359 → 379 |
| `FRVerifierImplOps` (S-F2) | **`shiftTargetI`/`shiftTargetS` on 18 coordinates** with `last = bnd[4 … 21]` (`lastOf`), `shiftTarget_meets` re-proved; **`eqPoint_eq`**, `eqPoint_shiftPair`, **`eqPoint_pad`**, **`shiftEqS_pad`**, `lastPad`, `getD_pad`, **`shiftTargetS_pad`**, `ptA_toArray`, `foldl_prod_range` | 382 → 457 |
| `FRVerifierImplNode` (S-F2) | `ptA16_pad`, **`shiftMaskS_pad`** | 489 → 497 |

`FRVerifierImpl` (`implCWith_meets`, `implC_meets`) is unchanged in text: its `shiftTarget` case
`fun k a b c _ => shiftTarget_meets k a b c` now discharges the 18-coordinate spec.

## 2. Item 1: the `finZ` defect

- **The op.** `finZ` ends with `.assertEq ((outsOf fi "Z2").getD 2 0) (fi.zhat.getD 0 0) allK`. In
  the dump (`ops-*.txt` line 66,090, all kinds): `assertEq r186 r54299 true`. `r186` is Z2's
  `lagrangeS` second output (`interpolateAt lNode … λ`, `P^z*(λ)`, `ops` line 192); `r54299` is
  `finRS`'s claim-0 value `α_Z` (`ẑ(r, λ)`).
- **Every kind the same way.** Z2's round and `finRS`'s claims 0–2 are kind-free (a leaf drops only
  claim 3, E's), so the assert is `allK`: L32, P30 and N30 check RS claim 1 identically. The other
  claims were already asserted (`zhat` 1 in `finLc`, 2 in `finSh`, 3 in `finE`, `nRS` in `finB′`).
- `assertEq` appends no register: `finZ`'s exports and every later register are unchanged.
- **`relZ`** (new) = `eq((ρ, r), r′)·â·b̂ = c_Z` **∧ `P^z*(λ) = α_Z`** (as `Val.eqv`).
  **`flag_finZ`**: `pureRun … (finZ …) = some (L, relZ …)`. There was no `relZ` and no
  `exec_finZ` before; `exec_finZ` is only named in `FRVIRSpec`'s header. The generic bridge is
  `exec_field`. `flag_finZ` had no user outside `FRVIRFinals`.
- **Controls.**
  - `relZ_iff` (F-valued registers): `relZ = true ↔ (first check) ∧ P^z*(λ) = α_Z`.
  - **`finZ_rejects` (−)**: with `P^z*(λ) ≠ α_Z`, `finZ`'s flag is `false`, whatever the first
    check gives. Before INT-4 no op read `zhat[0]`.
  - `finZ_accepts` (+): with them equal and the first check true, the flag is `true`.
- **The front (item 3).** No S-G statement changed or broke. `hFront`, `FrontObl`, `okRS oZ oSh` are
  stated over accepted traces of `gen`, and `gen` now rejects more traces, so `hFront` is easier to
  discharge (the theorems only get stronger). **S-G7 can now set `oZ κ es v := v = P^z*(λ)`**:
  `relZ_iff` gives it from an accepting `finZ`. Stale docstrings, not edited here because the
  modules are S-G's: `FRSoundnessFrPend` (header: "the implemented `finZ` binds nothing") and
  `FRSoundnessFrRS0` (header).

## 3. Item 2: ruling (c), `τ` of 18 coordinates

**`finSh` (S-0).**
- `τ = padB κ co z` and `r_blk = padB κ rs z`: the first `m − 14` registers, then `32 − m` copies
  of the zero register `z = b₀ + 4`. Both have 18 coordinates for L32, P30 and N30.
- `E₀`'s point is the constant `0^18`.
- `bnd` (22 entries) = the four boundary values, then the kind's last block `1^(m−14) ‖ 0^(32−m)`
  (from a new constant-`1` register).
- `linkWAll`'s packed points are unchanged: node only, and `τ`'s first 16 coordinates are already
  `m − 14`.
- Dump (`ops-*.txt` line 66,139): L32 `bnd` = `… 1^18`, P30 `… 1^16 0 0`, N30 `0^4 1^16 0 0`; `τ`
  = 16 S1 coordinates plus `r57444 r57444` (zero) for P30/N30.

**Specs and `_meets` (S-C, S-F2), op by op.**

| Op | `Meets` | Spec on 18 coordinates | Padded lemma |
|---|---|---|---|
| `eqPt` | inline (`eqPoint`) | `eqPoint_eq`: `eq` over `a.size` | `eqPoint_pad` (`eq_pad_zero` via `shiftPair_pad`) |
| `shiftEq` | unchanged (`a.size = b.size`) | `shiftEqS` is size-generic | `shiftEqS_pad` |
| `shiftTarget` | precondition `bnd.size = 22` | **`eq(ptA 18 τ, last)·h̃V(θ) + κ_s s̃V(θ)`**, `last = bnd[4 … 21]` (`shiftTargetAt`) | **`shiftTargetS_pad`**: at `τ ‖ 0^k` and `1^n ‖ 0^k` (`n + k = 18`) it is `FRShift.shiftTarget` on `n` coordinates (`shiftTarget_pad`, `eq_pad_zero`) |
| `shiftMask` | unchanged | reads `ptA 16` | `shiftMaskS_pad` |
| `slotW` | unchanged | operands `θ`, `r_pos` (10 each); no `τ` | — |

## 4. Deviations and statement changes (for the orchestrator)

1. **`shiftTarget`'s last block is an operand (`bnd[4 … 21]`). Ruling (c) does not cover this
   case.**
   - With a zero-padded `τ`, `eq(τ, 1^18)` is `0`. P30's last block is `1^16 ‖ 00`, so a kind-free
     18-coordinate `eq(τ, last)` cannot use a fixed `last`.
   - Choices:
     - A kind argument would make the op kind-dependent, against "they become templates".
     - **Chosen**: the kind-dependent part is constant registers in `bnd`'s `packFK`. The template
       computes `eq(τ, last)` (18 products) kind-free.
   - The op's signature is unchanged. Its `bnd` operand grows from 4 to 22 entries. A.8/A.9 need
     the row.
   - A node's target is still 0 (`bnd`'s values are 0).
2. **Statement and definition changes, each with its ruling.**
   - `flag_finZ`: new conclusion `relZ` (with the c-claim) and a `hin` with two more registers.
     Forced by item 1 (A.9 `finZ`, S-G6 finding 1).
   - `relSh`'s body (`τ`, `r_blk`, `E₀`'s point, `bnd`): ruling (c). `flag_finSh`'s text is
     unchanged.
   - `shiftTargetI`/`shiftTargetS`: ruling (c) and deviation 1.
   - `OpImpl.Meets`, the `shiftTarget` conjunct (`c.size = 4` → `22`): ruling (c) and deviation 1.
   - **Unchanged in text**: `implC_meets`, `implCWith_meets`, `implCWith_implT`, `acc_eq`,
     `finalLaw_of`, `finalLaw_of_run`, `hAcc_of`, `kstate_of_front`, `ExtIface`, every S-G
     theorem. Their meaning moves only through `gen` (the new assert, `finSh`'s operands) and
     `specC.shiftTarget`.
3. **L-circ**: no edit needed. `tplEqPt`, `tplShiftEq` and `tplShiftMask` are size-generic.
   `shiftTarget` is still an import, and `ImplT` does not mention it. The node circuit's
   `eqPt`/`shiftEq` instances now take 18 + 18 inputs instead of 16 + 16, so S-E11's row counts
   move by a few rows.

## 5. Re-dump (`logs/INT-4/dump/`, `fr-build-INT4/redump.sh`, `redump.log`)

- **ops 105,839** (HEAD = INT-3's 105,837; `gen` unchanged since `ebcc8f1`): **+2**. The two ops
  are `finZ`'s `assertEq` and `bndOps`' constant `1`.
- Last register `r97018` (+1). Skeleton registers 53,272 (unchanged).
- **asks = items = 8,891 (unchanged)**. **`items.json` is byte-identical to INT-3's** (sha256
  `71b533a2…`).
- **piSize 797,904 (unchanged)**; streamBytes, chainLen and fieldSizes unchanged.
- No `PENDING`. `diff` against INT-3: line 66,090 (the assert) and `finSh`'s block (66,138 on,
  renumbered registers).

## 6. V (N30), S-E8's method (`vt.sh`: core 27, 21 warm `runSeq` runs)

| Binary | Run | best | median |
|---|---|---|---|
| INT-4 | `vtime-N-a` | 219.6 ms | 231.5 ms |
| INT-4 | `vtime-N-b` | 224.9 ms | 239.3 ms |
| INT-4 | `vtime-N-c` | 224.6 ms | 238.3 ms |
| HEAD (S-E9's binary) | `vtime-N-head-a` | 212.1 ms | 224.6 ms |
| HEAD (S-E9's binary) | `vtime-N-head-b` | 220.4 ms | 229.4 ms |

- The VM was loaded during the runs, so the INT-4 − HEAD gap of about 5–10 ms is within run-to-run
  spread.
- The per-op profile (`prof-N.log`) puts the changed ops at **< 0.6 ms together**: `shiftTarget`
  0.25 ms, `eqPt` ×5 0.20 ms, `shiftEq` 0.10 ms, all 1,115 `assertEq` 0.39 ms.
- The 3.15 level (≈ 207 ms at S-E9 against INT-3's 168.7 ms) is S-E9's `maskRows` path in `evalM`,
  ruling (d), owned by S-E10. It is not this pass.

## 7. Checks

- **Axioms** (`logs/INT-4/axioms.log`, 22 names):
  - `acc_eq`, `implC_meets`, `implCWith_meets`, `implCWith_implT`, `finalLaw_of_run`,
    `finalLaw_of`, `hAcc_of`, `kstate_of_front`, `flag_finZ`, `finZ_rejects`, `finZ_accepts`,
    `flag_finSh`, `eq_pad_zero`, `shiftPair_pad`, `shiftTarget_pad`, `shiftTarget_meets`,
    `shiftTargetS_pad`, `shiftEqS_pad`, `eqPoint_pad`, `eqPoint_eq`, `shiftMaskS_pad`: only
    `propext`, `Classical.choice`, `Quot.sound`;
  - `relZ_iff`: `propext`, `Quot.sound`.
- **Source rule**: 157 files, 0 findings (`source-rule.log`).
- **Name clashes**: every new name has exactly one declaration in the entry (grep).
- **Sequential profiles** (`taskset` one core, `-DElab.async=false --profile`;
  `profile-<module>.log`):

| Module | wall | type checking | elaboration | max RSS |
|---|---|---|---|---|
| `FRVIR` | 20.1 s | 2.15 s | 7.39 s | 2.70 GB |
| `FRShift` | 11.6 s | 0.35 s | 0.50 s | 2.61 GB |
| `FRVerifierImplOps` | 16.5 s | 4.15 s | 0.43 s | 3.06 GB |
| `FRVerifierImplNode` | 15.0 s | 1.57 s | 0.50 s | 2.77 GB |
| `FRVIRFinals` | 35.6 s | 2.19 s | 16.9 s | 2.75 GB |

## 8. For P2 (`ir.rs`)

1. **`finZ`'s new assert**: `assertEq r186 r54299 true` (after `finZ`'s first `assertEq`). It is a
   plain `assertEq` of two F registers. The honest prover must produce RS claim 1's slices so that
   `α_Z = Σ_i eqZ(λ, ρ₁)_i s_i` equals Z2's `P^z*(λ)`.
2. **`τ` of 18 coordinates**:
   - `finSh`'s `τ` and `r_blk` are 18-element arrays for every kind, with P30/N30 coordinates
     16–17 = 0;
   - `E₀`'s point is `0^18`;
   - `eqPt`/`shiftEq` run on 18 coordinates (the same values as on 16 when padded);
   - `shiftMask` and `linkWAll` read the first 16.
3. **`shiftTarget`'s `bnd` has 22 entries**: `[s_lo, s_hi, h_lo, h_hi]` then the last block
   `1^(m−14) ‖ 0^(32−m)`. The value is `Π_{l<18} (τ_l L_l + (1−τ_l)(1−L_l)) · h̃(θ) + κ_s s̃(θ)`
   with `L = bnd[4 …]`. A new `const` F `1` op precedes it.
4. Registers after `finSh`'s start move by one (`r57446` on).

## 9. Open items

1. **A.8/A.9**: `shiftTarget`'s `bnd` of 22 (deviation 1); `finZ`'s row now matches A.9 (the
   c-claim is asserted).
2. **S-G7**: bind `oZ` (`relZ_iff`); refresh the two stale S-G headers (§2). The `τ` padding
   lemmas are what the S2 truth needs to connect P30/N30's 16-coordinate `FRShift` statements to
   the 18-coordinate ops.
3. **S-E11**: the `τ`-op templates on 18 coordinates; `shiftTarget`'s template reads `bnd[4 …]`.
4. **R-V** (the queued finals review) can start from `logs/INT-4/dump`.
5. `FRVIRSpec`'s header names a non-existent `exec_finZ` (S-0's module, untouched to avoid a
   rebuild; one-word fix: `flag_finZ`).
