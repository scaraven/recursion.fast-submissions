# S-E8 (track L-circ): JOURNAL — the `T_V` kill test (proved-equal fast twins)

Stage S-E8, 2026-10-28, HEAD `0e93332`. Build tree `logs/fr-build-e8` (a copy of S-E7's, with
`FRVIR`, `FRVIRSpec`, `FRVerifierImplOps` added to the symlinked set in `snap.sh`). Logs in
`logs/S-E8/`. Every lean/lake/probe run in the 16 GB scope; V timed with `vt.sh` (`vtime v N 21`,
21 warm `runSeq` reps, `taskset -c 30` or `28`), per-op profile with `pr.sh` (`vtime prof N`).

## Baseline

- V (N30): **235.0 / 231.2 / 232.2 ms best, 241.8 / 238.5 / 250.9 ms median** (`vtime-N-0{a,b,c}.log`).
  S-E7 measured 227.4 ms best on 9 reps; today's core is a few ms noisier.

## Item 1: `dotKF` → `dotKFF`

- `FRVIR`: `fAt` (an F read in place from 16 bytes, `fAt_eq : fAt b o = F.ofBytes (bytesAt b o 16)`),
  `dotKFGo`/`dotKFF` (one tail-recursive loop over `min (col.size / 16) w.size` rows),
  `dotKFF_eq : dotKFF w col = dotKF w col`. `evalOp`'s `dotKF` case runs `dotKFF`.
- Proof repairs: `FRVIRSpec.exec_posHead` (`dotKFF_eq` in its `simp only`), `FRVIRTplExt`'s
  `dotKF` case (`rw [dotKFF_eq]`). No statement changed.
- `congr 1` on the fold timed out at `whnf` (it unfolds `K`'s `+`); `congrArg (List.foldl …)` instead.
- V: **208.95 / 206.89 ms best, 219.0 / 224.5 ms median** (`vtime-N-1{a,b}.log`). Profile
  (`prof-N-1.log`): `dotKF` 30.7 → **7.2 ms**.

## Item 2: `tensorW` → `Impl.tensorWF`

- The brief's "set bits only" does not pay: a micro-benchmark (`vtime tw`, `tw-proto*.log`) shows
  `wAtT` is ≈ 30 % of `tensorWI`; the rest is the 7 `K` products and the 7 `r_v · Ŵ` `K` products.
- `FRVerifierImplOps`: `wByte` (60 tables of 256 `F`, one per `(v, byte b)`, computed once),
  `wB`/`wB_eq`, `wAtF` (3 lookups) with `wAtF_eq : wAtF v j = wAtT v j`, `tensorWF` (`wAtF`, and
  `smulF` for `r_v · Ŵ`) with `tensorWF_eq : tensorWF j r = tensorWI j r`. `implCWith.tensorW :=
  tensorWF`; `implCWith_meets` uses `(tensorWF_eq j r).trans (tensorW_meets j r)`,
  `implCWith_implT` uses `funext tensorWF_eq`. `Circ.ImplT`'s field is unchanged.
- **Finding:** `2 ^ (8 * b)` on `ℕ` runs as a loop in compiled code (the first `wAtF`, with
  `j / 2 ^ (8 * b)`, was *slower* than `tensorWI`: 44.7 vs 43.7 ms per 1,627 ops). With literal
  divisors (`j / 256 % 256`): **26.6 vs 44.2 ms per 1,627 ops (n = 7), 75.6 vs 125.3 (n = 20)**
  (`tw-proto3.log`). The same applies to `idxOf`'s `2 ^ (i * b)` and `natLE`'s `256 ^ i`.
- V: **206.2 / 204.9 ms best, 213.1 / 210.5 ms median** (`vtime-N-2{c,d}.log`); profile
  `tensorW` 12.3 → 10.9 ms (`prof-N-2b.log`).

## Item 3: `maskRows`

- A twin is not possible here: `FRVIRFinals.relLc` (not mine) states `maskRows` and `flag_finLc`
  closes by `simp only [evalOp …]; exact ⟨_, rfl⟩`. So `maskRows`' **body** changes, and its A.8
  reading becomes the lemma `maskRows_eq : maskRows kindW rowW = rowW.mapIdx fun k w => w * maskOf
  kindW k`, with `maskOf` the old per-row sum verbatim.
- The new body computes `maskOf` for rows `≤ pinEnd = 1152` and one shared value past it
  (`isZeroRow_of_gt`, `maskOf_of_gt`). `FRVIRTplTab.tplMaskRows_ok` repaired by `maskRows_eq, maskOf`
  in its `simp only`.
- V: **200.4 / 201.4 ms best, 207.3 / 210.7 ms median** (`vtime-N-3{a,b}.log`); `maskRows`
  8.5 → **2.5 ms** (`prof-N-3.log`).

## Item 4: `idx` → `idxOfF`

- `FRVIR` (section `IdxF`): `dByte` (a digest byte, `0` past 32), `dWin` (four bytes from `k`),
  `idxOfF b a i := if b ≤ 24 then dWin a (i b / 8) >>> (i b % 8) % (1 <<< b) else idxOf b a i`.
  `idxOfF_eq : idxOfF b a i = idxOf b a i` holds for **every** `b`, `a`, `i` (the zero bytes past
  32 make the window exact even when `i b ≥ 256`), so no parameter side condition is needed.
- Proof: `natLE_sum` (natLE as a range sum of `dByte`, any `N ≥ 32`), `sum_lt_pow`, `natLE_split`
  (`natLE a = low + 256^k (dWin a k + 2^32 H)`), then `Nat.add_mul_div_left`,
  `Nat.add_mul_mod_self_left`. `idxOf`, `natLE`, `nodeQ` untouched.
- `evalOp`'s `idx` case runs `idxOfF`; `FRVIRSpec.exec_posHead` gets `idxOfF_eq` in its `simp only`.
- V: **177.8 / 183.7 ms best, 186.0 / 204.0 ms median** (`vtime-N-4{a,b}.log`); profile `idx`
  19.8 → **0.84 ms** (`prof-N-4.log`).

## Item 5: `askNode` → `nodeQF`

- `FRVIR.nodeQF i l r := ⟨#[tag…, i.toUInt8, 0] ++ l.toArray ++ r.toArray⟩`, `nodeQF_eq : nodeQF i l r =
  nodeQ i l r`; `evalOp`'s `askNode` runs it; `FRVIRSpec.exec_merkleOps` gets `nodeQF_eq`.
- Micro-benchmark (`vtime nq`, `nq-proto.log`, per 7,552): `nodeQ` 10.1 ms, `nodeQF` 2.9 ms,
  **the oracle's compare 0.12 ms** (`ByteArray`'s `DecidableEq` is `lean_sarray_dec_eq`, a memcmp).
  The profile's `askNode` also counts the probe's own `randDigest` answers (8.9 ms per 7,552), which
  `runSeq` does not run.
- V: **172.3 / 172.1 ms best, 184.2 / 179.8 ms median** (`vtime-N-5{a,b}.log`).

## Item 6: the rest of the profile

- `piDigestAt` → `digestAt` (one 32-byte slice; `digestAt_eq : digestAt q o = bytesAt q o 32`;
  `FRVIRSpec.exec_posTail` repaired). Bench (`pd-proto.log`): `bytesAt … 32` 4.8 ms vs slice 0.7 ms per
  7,555. Alone it is not measurable (871 ops).
- `piDigest` (7.2 ms) with `digestAt`: **blocked** — `FRVIRFinalsSF.flag_finB'` closes by
  `exact ⟨_, rfl, rfl⟩` over `bytesAt`. Verified on a private copy in the build tree (not the
  worktree): adding `digestAt_eq` to its `simp only` is the whole repair; V then **164.1 / 167.3 ms
  best** (`vtime-N-6x-{a,b}.log`). Reverted; `snap.sh` restored HEAD's copy.
- `eqTable` (5.2 ms; `t − t·x` halves the products), `piElem`/`piElemK` (`fAt`): blocked the same way
  (`FRVIRCompile` unfolds `eqTab`; `FRVIRFinals*` state `eqTab`, `pe`, `sv`, `finV` by `rfl`).
- The rest above 3 ms is field arithmetic (`mulK`, `addK`, `rsWeight`, `phiRS`, `tensorW`'s and
  `dotKF`'s products) or `evalM`/`walkAB`; no `perf` (`perf_event_paranoid = 4`).
- Final state V: **173.4 / 170.9 / 169.4 ms best, 176.9 / 178.6 / 177.4 ms median**
  (`vtime-N-6{a,b,c}.log`, `prof-N-6.log`).

## Item 7: the child's fused walk

- Prototype (`vtime cw`, `cw-proto.log`): `Â₀(τ_lo, σ_lo)`, `B̂₀(τ_lo, σ_lo)` by two `eq` tables over
  14 bits (3.2–5.0 ms each) and one fused `walkImpl` (8.9–9.3 ms): **15.2 / 15.8 / 17.8 ms**. Computed
  once and shared by both slots, this is the blueprint's 16 ms.

## Controls, build, audit

- Controls (`decide +kernel` through the twins): `dotKF_pos/neg`, `idxOf_pos/neg`, `nodeQ_pos/neg`,
  `bytesAt_pos/neg`, `maskOf_pos/neg` (end of `FRVIR`), `tensorW_pos`, `tensorWF_pos`, `wByte_neg`
  (`FRVerifierImplOps`). A first `tensorW` control through `wByte` cost 7 s of kernel (a 256-entry
  `Array.ofFn` per entry); the final ones cost ≈ 4 s together.
- `lake build FR` green (1 m 46 s incremental, `last.log`); `#print axioms` of `acc_eq`,
  `implC_meets`, `implCWith_meets`, `implCWith_implT`, `runSeq_runIR`, every `_eq` and every control:
  only `propext`, `Classical.choice`, `Quot.sound` (`axioms.log`). Source rule: 133 files, 0 findings.
