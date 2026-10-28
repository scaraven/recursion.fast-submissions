# S-G8 JOURNAL

Base HEAD `0751f44`. Build tree `logs/fr-build-SG8` (copied from `fr-build-SG7` with its `.lake`;
`snap.sh` now also symlinks `FRSoundnessAccSem` for item 3). Logs in `logs/S-G8/`. Every lean/lake
command runs in the 16G (builds) / 12G (single files) capped scope with a `timeout`. No sub-agents.

## Item 1: `pendZ_pendBad` (done)

- New module `FRSoundnessFrBind` (imports `FRSoundnessFrL`, `FRSoundnessFrS`).
- `trueL_zero : trueL (kindOf es) L es 0 = (pzT L es).eval (lamL es)`. The bit index
  `i + 128 v` with `i = σ + 64 y` against `σ + 64 u`, `u = y + 2 v` (`sum_range_mul_split`,
  `sum_eqAtR_split 1 (m − 7)`); `cwL_zero` reads `eqZS`'s entry `σ + 64 y` as
  `lagrangeWeight sNodeF λ σ · eqAtR(ρ₁) y` (bit 6 via `Nat.testBit_div_two_pow`); `zrL_drop`:
  Z1's point minus `ρ₁` is RS claim 1's high point `zPtL`.
- `pendZ_pendBad {oSh} (h : PendZ L es) : PendBad (okRS oZ oSh) L es` at `j = 0`.
- First try failed on `set n := nrP 0 κ` (the binder types `Fin (2 ^ nrP 0 κ)` were not
  abstracted, so `hq` did not fire); written with `nrP 0 κ` throughout.

## Item 2: `zlmFR`; the leaf's Lc (done)

- New module `FRSoundnessFrZM` (imports `FRSoundnessFrBind`).
- **`zlmFR`** (one `ZLM` for all kinds): kind `j` = `blockKinds[j]` (`bkOf`); `Ak`/`Bk` =
  `kMat circuitR1CS.A/B`: `0` on the kind's `zeroRows`, identity for `free`, the circuit's row
  otherwise (the verifier's `maskRows` shape); `Ind` = `[bkOf j = nodeBK t]` (node), `[j = 0]`
  (leaf, `chain`); `Et` = `nodeE` (node), `chainE` (leaf).
- Pins: `kindTarget_isNone`, `blockTarget_isNone`; per kind `pins_*`; `nodeKind_pins`: each
  target of `nodeKind blk` pins exactly `zeroRows (nodeBK blk)`; `pins_chain`.
- Layout: `chained_unique` (non-overlap from `nodeLayout_chained`) and `ind_iff`:
  `Layout.Ind b blk = true ↔ b = nodeBK blk` for `blk < nodeBlocks` (the verifier's `kindInd`
  selector is `zlmFR`'s node indicator; for INT-5's node L).
- `zHolds_iff_blocks` (generic); **`zHolds_iff_truthZN`** (node; free blocks by `z² = z` on bits),
  **`zHolds_iff_truthZ`** (leaf: `truthZ (fun _ => chainTarget) (2^(m−14))`).
- **`peL_node`**: `targetSNodeS r = Array.ofFn (peL zlmFR es)`; **`peL_leaf`**:
  `targetSLeafS 16 r = …` (L32: the two high block coordinates sum out), for any register `r` with
  `r[l] = coordAt es 2 l`, `l < 17` (`zrL_append`).
- `zlmFR_bits`, `zlmFR_indKinds`.
- `trueL_one` (every kind: RS claim 2's true value is `ẑ(r_k, r_blk)`), `zfL_leaf`,
  **`pendLc_pendBad`** (leaf), **`rejLc2_ok`** (`rejOK_at 97`).
- Lesson: `sed -i` on `src/X.lean` replaces the symlink by a copy. Edit only worktree files.
- Dispatching `exact pins_*` under `first` hit max recursion (failed unifications unfold the
  targets); `with_reducible exact` fixed it.

## Item 3: `accept_fields` (done)

- `FRSoundnessAccSem`: new `exAt outs zh fs b ex k` (the exports `runFields` passes field `k`).
  `fields_ok`'s `∃ exk` is replaced by `exAt outs zh fs R.size ex k`; `accept_fields`' `finRS`
  conjunct has `ex = #[]`, and its rest conjunct has `zhat = (finRS ⟨outs, [], #[]⟩
  skeleton.2.next).2` and `ex = exAt … fin.rest (next + opsOut finRS) #[zhat] k` (the `∃ zh`
  and both `∃ exk` are gone). The proof already used these witnesses; `rw [hsz]`, `rw [hn]`.
- `FRSoundnessAccLog` (`finLog_of_run`): a proof repair. It rebuilds the old existential form
  right after the call (4 lines). No statement there changes.
- `lake build FR`: green, 2,386 jobs (`logs/S-G8/build-FR.log`).

## Stop

Items 1–3 are done and checked (axioms, source rule, profiles). Items 4–7 are the assembly. It
needs every phase lemma's exact statement in view, so it goes to a fresh pass (RESULT §5).
