# INT-5 journal: blueprint 3.16 (R-V-M1, R-V-M2, R-V-m1) in S-0, S-C, S-F2

Worktree `v4/flock-recursive`, HEAD `f9e2afc` (3.16 blueprint). Build tree `logs/fr-build-INT5`
(copy of INT-4's; `snap.sh` with MINE = this pass's modules). Logs in `logs/INT-5/`.

## 2026-10-28

- Read TRACK-RULES, R-V finals review, BLUEPRINT changes 23 / A.8 / A.9 / A.11, INT-4 RESULT.
- HEAD baseline: `lake build FR` green, 2,382 jobs (`build-head.log`, 4 min 20 s, rebuilt the
  symlinked modules).
- Design decisions:
  - **`rsWeight`'s `β` operand, kind-free.** The op takes `β`; claim index 1 (Lc) carries
    `B_β^{2^k}`. A leaf passes `β = 1` (`keep isNode β 1`, computed in `finLc` and exported):
    `B_1 = Σ_κ Ind_κ = 1` because the kinds partition `[0, 2^q)` (`free` = `[wmBase, 2^q)`). So the
    op has no kind argument and its template is uniform.
  - `kindFoldWeight` stays as a dead constructor (value 0): removing it would edit L-circ
    (`FRVIRTplExt`, `FRVIRCompile`) while S-E10 has those files open.
  - The free term of (ii) is placed after `hornerOps`, and (ii)'s assert moves to the end, so the
    existing register numbers of `finLc` (and its export `b + 36`) do not move.
- **S-C** `FRRingSwitch.rsWeight_kind_eq` (+ `hiIdx`, `kindFac`, `kindFac_frob`): generic over a
  char-2 ring, 0/1 indicators (disjointness not needed: Frobenius is additive). Green.
- **New module `FRKindWeight`** (spec `kwS`, impl `kwI`, `kwI_eq` for `n ≥ 16`; `plan` of 23 items
  checked against `Layout.kindIvs` by `decide +kernel`; partition `part_one` → `kwS_one`; controls
  `kwS_cube`, `kwS_hashA` (+), `kwS_hashA_ne_plain` (−)). Green.
- **`FRVIR`**: `Op.rsWeight r pts κ β act ρ` (β gated by `act`: `1` where it fails; `gen` passes
  `isNode`), `OpImpl.rsWeight … κ β ρ`, `Meets` precondition `+ 23 ≤ ρ.size`; `Val.isBit`,
  `evalOp (.assertBit a act) = .vals [] (!act κ || isBit a)`; `nodeKindW`; controls `maskOf_pos`
  (now: `free` weight 0), `maskOf_free_old` (−), `isBit_pos/neg`, `assertBit_rejects` (−),
  `assertBit_accepts` (+). Design change from the first plan: β is gated inside the op (no
  `finLc` export), because a new register reference in `finPf` beyond the skeleton would falsify
  S-G's `pfRefs_lt` ("`finPf` reads only the skeleton's registers").
- **`FRVIRFinals`**: run kit moved in (`pureRun_append` from SF, `pureRun_rebase` from SG,
  new `pureRun_seq`); `dotOps`/`dotVals`/`dotAcc`, `run_dotOps` (induction), `dotOps_noAsk`;
  `finLc = lcHead ++ dotOps … 64 ++ lcTail`; `relLc` = `((i) && (iii)) && (ii)` with
  `(ii)`: walk (node vector `nodeKindW`) `+ Y + αY`, `Y = lcFree`; `flag_finLc` re-proved in three
  blocks (head by simp with `?`-free witnesses via `apply Exists.intro`; the 64-term sum by
  `run_dotOps`; the tail by simp). Pitfall: `List.getD_eq_getElem?_getD` in the simp set rewrote
  `fi.zhat.getD 1 0` and broke `rd_app_left _ _ hz`; named holes `?V1` are not assignable by `rfl`.
- **`FRSpartan.linM_free_mle`**: `free`'s column weight at `r_k = (r₁, r₂)` in closed form.
- **`FRVIRFinalsSG`**: `finPf`'s `rsWeight` passes L3β's `β` and `Kind.isNode`; `w0V`, `pfRefs`
  (+ L3β's β), `flag_finPf` proof updated (one `rr`, `rsW` unfolded before the kind split).
- **`FRVerifierImplOps`**: `wEvalKC` (claim 2's stage fold), `rsWeightI`/`rsWeightS` with `β`,
  `kwSL`, `wEvalKC_fold`, `wEvalKC_eq`, `rsWeight_meets` (+ `23 ≤ ρ.size`).
- **L-circ**: `FRVIRCompile.opOut`: `assertBit` → `foreign := true` (it was `{ slots := [] }`; its
  soundness `opOut_sound` needs the flag implied by rows or the op foreign). One line, forced by m1.
- **S-G proof repairs** (`FRSoundnessAccLog`, statements unchanged): `noAsk_finLc` (split by
  `dotOps_noAsk`; plain `simp` timed out on 64 unfoldings), `pfRefs_lt` (one more case: L3β's β).
- `lake build FR` green (2,389 jobs, `build-FR-1.log`).
- Re-dump: ops 105,839 → 106,106 (+267: 4 + 256 + 7), items/piSize/items.json unchanged.
- Toy check `scripts/kindcheck.py` (GF(2^8), 3 seeds): (iii) holds with the kind weight, the Φ form
  equals the item algorithm, the plain weight gives `Σ v_i` (R-V's counter-situation), β=1 plain.
- V (N30): INT-5 314.7 / 322.4 ms best vs INT-4's binary 219.1 / 216.1 interleaved on core 30.
  `prof`: rsWeight 7.2 → 40 ms (K products ~0.45 µs, ~640 per stage); evalM 110 → 193 ms (the
  node plan: keys 83 → 89, pieces 5,062 → 5,148 per slot; rows after `finLc` shift by 267).
- Dropped flag_finLc's maxHeartbeats option (default suffices, 40 s); final `lake build FR` green, 2,389 jobs (`build-FR-2.log`). Profiles, axioms, source rule logged. RESULT written.
- HEAD moved to feca303 (S-G8, S-E11, S-G9) during the pass; re-snapshot, `lake build FR` green 2,397 jobs (`build-FR-3.log`) with no repair. V on feca303: 233.2 / 226.3 ms best; evalM 83 ms (no regression with S-E11's evaluator), rsWeight 38 ms.
