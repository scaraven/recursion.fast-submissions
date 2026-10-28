# S-G4 RESULT: `hFin` discharged

Base: HEAD `b1d8c46`. HEAD moved to `937e14d` (S-E8's commit) during the stage; the snapshot
(`logs/fr-build-SG4/snap.sh`) re-reads HEAD, so everything below is built and checked against
**`937e14d`**. S-G4's modules are symlinked into the snapshot; no other track's module was
edited.

`lake build FRSoundnessAccLog` is green in `logs/fr-build-SG4` (all nine S-G4 modules and their
imports). There is no `sorry`.

- **Axioms** (`logs/S-G4/axioms.log`, every theorem of the nine modules, 141 declarations): only
  `propext`, `Classical.choice` and `Quot.sound`.
- **Source rule** (`python3 -I .contract/scripts/source-rule.py submissions/flock-recursive`):
  147 files, 0 findings (`logs/S-G4/source-rule.log`).

## 1. The result

```lean
theorem finLog_of_run {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r)
    {vk c : Digest} {π : Proof} {k : Kind} {L tr : Log}
    (hb : ¬ Bad L) (hπ : π.size = piSize) (hk : FR.kindOf π = .snark k)
    (hsem : semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true)
    (hin : ∀ e ∈ tr, e ∈ L)
    (hStart : ∀ y, refPhases impl k ⟨vk, c, π⟩ phases 0 ctx₀ #[] tr = some y →
      rd (#[] ++ y.1.toArray) (claim0 ⟨skeleton.2.outs, [], #[]⟩ "P1") = .k (c₀ L (fsOf tr items)))
    (hW0 : ∀ y, refPhases impl k ⟨vk, c, π⟩ phases 0 ctx₀ #[] tr = some y →
      ∀ (fi : FinIn) (r' : Array Val), fi.outs = skeleton.2.outs → ExtA (#[] ++ y.1.toArray) r' →
        w0V impl k fi r' = wHatL W₀ L (fsOf tr items) 0) :
    ∃ yv, FinLog W₀ c₀ L (fsOf tr items) yv
```

The witness is `yv i q := (rd R ((ysOf fi i).getD q 0)).toK`, the values of the fold registers.

**`hAcc_of_fin`** is `hAcc_of` with `fin := sfFinals finP finPf` and `hFin` discharged by
`finLog_of_run`. It keeps `hE` and adds `ht`. The named hypotheses left are the front's three:
- `hStart`: `claim0 "P1"` holds `c₀ L es`;
- `hW0`: `w0V` is `wHatL W₀ L es 0`;
- `hFront`: `¬ RejF`.

**`tensorW_implC`** supplies `ht` for `implC`: it is the `tensorW` field of `implC_meets` as at
HEAD.

- **`ex`/`zhat`**: they stay existential. `finP` and `finPf` read only `fi.outs`. So does `w0V`:
  `coordsR "RS1"`, `outsOf "B'"` and `pfPts` all read `outs`. Both `hW0` and `finLog_of_run`
  quantify over every `fi` whose `outs` are the skeleton's, so the front needs neither `ex` nor
  `zhat`.

## 2. What was built (code lines from `scripts/loc.py`, `logs/S-G4/loc.log`)

| Module | Total / code / thm | Content |
|---|---|---|
| `FRSoundnessAccSeg` | 247 / 184 / 20 | **2a.** `refPhases_at`, `phase_at` (phase `k`'s `refPhase` run at `cAt k`, `ExtA` into the skeleton, its flag, `(fsOf tr items).drop (phStart k) = fsOf trk …`), `skeleton_outs`, table rows (`phases_lvl`, `phases_pf`, `phaseIx_P1 = 26`, `phaseIx_Pf = 51`) |
| `FRSoundnessAccVal` | 243 / 185 / 14 | **2b, `.rounds`.** `roundsT_vals`, `SkRun`, `cAt_succ`, `phase_entries`, `rounds_view` (`cl ↦ rSum … 0`, `rs[j] ↦ chK`, last `↦ rVal … (K−1)`, in-phase checks, `foldR`) |
| `FRSoundnessAccEq` | 192 / 129 / 14 | **5.** `eqTab_getD` (`eqTab r` at `q` is `eqBits r |r| q`), `dotKF_eq_sum`, `fhVal_mle`, `tensorWS_unit`, `encVal_eq_encAt` |
| `FRSoundnessAccQry` | 140 / 112 / 5 | **2b, `.queries`.** `stepsT_path`, `posT_path`, `posAllT_path` (the trace's Merkle steps are `openPath … runLog L = some capD`) |
| `FRSoundnessAccLvl` | 333 / 270 / 17 | `pos_view`, `coords_view`, `queries_view`, `final_view`, `finV_zero`, `genPhase_out_lt`, `skeleton_out_lt` |
| `FRSoundnessAccPf` | 140 / 105 / 9 | `p1_facts`, `pf_facts`, `kc_facts` (`kcOf ↦ kcAt`, P3's `chF`), `lvl_facts` |
| `FRSoundnessAccCol` | 179 / 145 / 10 | `capDig_eq`, `phaseOff_add_le`, `fieldOff_add_le`, `ys_facts` (`FinLog.cols` on registers) |
| `FRSoundnessAccW` | 242 / 194 / 15 | **6.** `tailList`, `tailList_eq`, `tail_vals` (`tailRegs ↦ ptL`), `lvStepV_eq`, `wV_eq` |
| `FRSoundnessAccLog` | 523 / 435 / 36 | `noAsk_finZ/Lc/Sh/Lr`, `kindOf_fsQ`, `finalAt_fsQ`, `pfRefs_lt`, `accVal_kc`, **`finLog_of_run`**, **`hAcc_of_fin`**, `tensorW_implC` |
| **Total** | 2239 / 1759 / 140 | |

### By item

1. **Step 2a (phase segments).**
   - `refPhases_at` follows `refPhases_chain`'s style. `phase_at` instantiates it on the table.
   - The FS segment from `phStart n` comes from `fsOf_append` and `phStart_eq_sum`, with no new
     `decide`.
2. **Step 2b (values by shape).**
   - **`.rounds`** (`roundsT_vals`, `rounds_view`, `p1_facts`, `pf_facts`):
     - `cl = c₁ + c₂` (`rSum … 0`);
     - `rs[j] = chK` of squeeze `j` (`sAt`, `pfP`);
     - the last register is `gK` (`rVal … (K−1)`, so `c1` and `clR2 … 7`);
     - the in-phase checks hold (`FinLog.rnd`, `rndPf`).
   - **`.queries`** (`ys_facts`):
     - `ysOf` holds `dotKF (eqTab sᵢ) col_q = Σ_r eqBits sᵢ ℓ r · col_q[r]`;
     - the register 3 below it holds `qPos`;
     - `posAllT`'s flag gives the Merkle path to `capDig` on `L` (needs `¬ Repeated L`).
   - **P3** (`kc_facts`): the `kcOf` registers hold `kcAt` (`chF` coordinates).
3. **Step 5.** `implC_meets` is used as at HEAD, for its `tensorW` field.
   - `eqTab`/`dotKF` ↔ `eqBits`/`mle` are plain lemmas in `FRSoundnessAccEq`, not in
     `FRVerifierImplOps`.
   - The spec-to-spec lemmas:
     - `encVal_eq_encAt`: `hornerVal` with `tensorWS p e_v = Ŵ_v(D[p])` is
       `encAt κ 4 m p`, when the π elements past `2^mLog` are zero;
     - `lvStepV_eq`: the `tensorTwin` in `wHatL`'s step.
4. **Step 6 (`relPf`).**
   - `wV ↦ wHatL 4` (`wV_eq`): induction over `lvsV`, with `tailRegs ↦ ptL` (`tail_vals`).
   - `finHat ↦ mleN 7 finalAt pfPt` (`fhVal_mle`, `finalAt_fsQ`).
   - `padV`: S-G3's `padV_eq`.
   - `claimN Pf ↦ clR2 … 7`: `pf_facts`, by `rfl`.
5. **Assembly** (`finLog_of_run`):
   - `accept_fields` with `noAsk_sf`;
   - `flag_finPLow`, `flag_finP4` and `flag_finPf` on each field's registers `Rk`, with the `hin`
     bounds from `skeleton_out_lt` and `pfRefs_lt`;
   - `pureRun_det` gives the relations;
   - the register facts transfer by `ExtA`.

   FinLog's fields come from: `link` ← `relPLow`; `pf0` and `enc` ← `relP4`; `fin` ← `relPf`;
   `cols` ← `ys_facts`; `rnd`/`rndPf` ← the rounds views; `start` ← `hStart`.

## 3. Build and kernel times

Sequential profiles (`taskset -c 0 lake env lean -DElab.async=false --profile
-Dprofiler.threshold=100`), logs in `logs/S-G4/time-*.log`:

| Module | Wall | Type checking | Max RSS |
|---|---|---|---|
| `FRSoundnessAccSeg` | 11.4 s | 427 ms | 2.78 GB |
| `FRSoundnessAccVal` | 9.0 s | 677 ms | 2.79 GB |
| `FRSoundnessAccEq` | 7.8 s | 132 ms | 2.79 GB |
| `FRSoundnessAccQry` | 6.9 s | 191 ms | 2.80 GB |
| `FRSoundnessAccLvl` | 17.2 s | 1.28 s | 2.85 GB |
| `FRSoundnessAccPf` | 6.9 s | 170 ms | 2.79 GB |
| `FRSoundnessAccCol` | 8.8 s | 944 ms | 2.86 GB |
| `FRSoundnessAccW` | 12.6 s | 646 ms | 2.83 GB |
| `FRSoundnessAccLog` | 18.2 s | 799 ms | 2.91 GB |

- Each wall time includes about 4 s of imports.
- In total, 4.4 s of the measured time is type checking (kernel).
- The slowest single steps:
  - a `congr` in `lvStepV_eq` (807 ms);
  - `simp` in `noAsk_finSh` (734 ms);
  - `simp` in `genPhase_out_lt` (≈ 300 ms each).

## 4. Controls

| Definition | Positive | Negative (non-vacuous) |
|---|---|---|
| `psItems` | `psItems_ctl.1`: one phase's items | `psItems_ctl.2`: two seeds are not one item |
| `cAt` | `cAt_zero` (`ctx₀`); `cAt_one_next.1` (next = 7 after the seed) | `cAt_one_next.2` (≠ 0) |
| `SkRun` | `skRun_of_accept`: every accepted run of a no-ask `gen fin` is one | `not_skRun_nil`: the empty trace is not |
| `tailList` | `tailList_four`, `tailList_one_head` (level 1's tail starts at `s₁[1]`), `tailList_len.1` (19 at `m = 32`) | `tailList_len.2`: the `m = 30` tail has another length |
| `tLen` | `tail_len` (= `mLog κ (k−1)`, both ladders) | `tLen_ne`: `tLen 32 1 ≠ tLen 30 1` |
| `eqTab` bit order (lemma `eqTab_getD`) | `eqTab_ctl`: `eqTab [0,1]` is `1` at index 2 and `0` at index 1 | `eqTab_rev_ne`: reading coordinate `v` against bit `1 − v` gives a different value at index 1 |

`FinLog` itself has no positive instance here. As S-G3 noted, building one needs a log with
Merkle openings. `finLog_of_run` is the positive direction from an accepted run. S-G3's
`finLog_rounds_of_acceptTail` is the converse on the round fields.

## 5. Deviations

1. **A new theorem `hAcc_of_fin`, not an edit of `hAcc_of`.**
   - `hAcc_of`'s `hFin` quantifies over all `k c π` without `FR.kindOf π = .snark k`.
   - FinLog's fields are in terms of `kindOf es`, and `kindOf es = k` needs π's kind byte
     (`kindOf_fsQ`).
   - So `hAcc_of_fin` repeats `hAcc_of`'s ten-line proof and passes `hk` to `finLog_of_run`.
   - `hAcc_of`'s statement is unchanged. It is also general in `fin`, while `hFin` holds only
     for `sfFinals finP finPf`.
2. **`ht : impl.tensorW = Impl.tensorWS` is a hypothesis** of `finLog_of_run`/`hAcc_of_fin`.
   `tensorW_implC` discharges it for `implC` (`implC_meets`).
3. **`hW0` quantifies over register files extending the skeleton's** (`ExtA R r'`). `finPf` runs
   on such a file `Rk`. Without a `w0V` congruence lemma, the transfer is asked of the front: the
   front's `w0V` reads only skeleton registers, so it holds on any extension.
4. **Small `decide`s on the phase table and the ladders** (no program, no item list). Each is
   recorded here because the rule asks for certificates:
   - `phaseIx_P1`, `phaseIx_Pf`: the names of `piopPhases`' 26 rows (and the five-row level
     list);
   - **`phaseOff_47 : phaseOff 47 fFinal = 0`**: the byte counts of rows `0 … 46` toward field
     15, ≈ 170 ms. It is needed to read the final message at the verifier's offset
     (`finalAt_fsQ`). A certificate next to S-H2's `capOffL_fsMsgs`
     (`fsMsgs.getD (phStart 47) none = some (finOff, 4096)`) would replace it;
   - `capOff_abs` (`absOff fCaps (capOff i) = capOffL i`), `cap_eq`, `lvl_facts`, `tail_len`,
     `tLen_ne`, `hEll_pos`: 5 levels × 3 kinds of ladder numbers;
   - the cap positions and messages use the existing `capPos_eq`, `capOffL_fsMsgs` and
     `fsMsgs_ctl`.
5. **`queries_view` needs `¬ Repeated L`** (from `¬ Bad L`). The Merkle path's `runLog` takes
   the first entry for a query.

## 6. Open questions

1. The owner of `FR.lean` should add `import FRSoundnessAccLog`. It is a new root and imports
   `FRSoundnessAcc`, `FRNodeCircuit` and `FRXReadLv`.
2. `hStart` and `hW0` are the front's (after INT-3):
   - `hStart` is what `finB′`'s `relB` asserts about `claim0 "P1"`;
   - `hW0` is `weight_mle`/`mleN_w0F` on `w0V`'s registers.

   Should `kstate`'s obligation list replace `hFin` by these two?
3. S-H2 could add `phaseOff_47` as a certificate in `FRXChainFlock` (deviation 4).
4. `finLog_of_run` fixes `fin := sfFinals finP finPf`. If `finC`'s `finPf` changes, only
   `noAsk_sf`, `rest_eq` and the `finPf` step need to follow.
