# T4 RESULT: the Ligerito tail (P1.i … Pf) at revision 4.1's `seq4`

- **Base.** HEAD `7e14be6` at the start; HEAD `4841734` (P4a, P4b pass 1) at the end. `snap.sh`
  picked up the new HEAD, and the final build ran on it. **Build tree** `logs/fr-build-T4`, a copy of
  `fr-build-SG13` with its `.lake`, on `logs/org20`; `MINE.txt` lists the 11 new modules. Logs are in
  `logs/T4/`. Journal: `T4-JOURNAL.md`.
- **Constraints.**
  - Every lean/lake command ran in the 16G scope (12G for single files) under `timeout`.
  - No sub-agents. Nothing committed.
  - No existing module was edited and no existing statement changed. The worktree's modified
    `FRVIR*` files (S-E13's) were not touched.
  - Every new name is in namespace **`FR.Snd.T4`**. No other module uses it (grep). The only
    constants the modules create outside it are private auto-generated `match_1` lemmas
    (`scratch/NsT4.lean`).

## Status

| Item | State |
|---|---|
| The tail at `seq4` (`StepA…E`, `Truths`, `Hide`, `Walk`, `Weights`, `Fold`, `Tail`, `TailD`, `TailO`, `TailM`, `Compose`, `LigFinal`) | **Done**. Ported by copy, with the position map `+14` and the six-kind ladder. |
| `muT4`, `PhaseObl4`, `kstate`'s `empty`/`step` via `G.muG_step_of fsRnd4_ok fsRnd4_zero` | **Done**: `T4.muT`, `T4.PhaseObl`, `T4.muT_empty`, `T4.muT_step`, and `T4.muT_laws_of_front` from `FrontObl`. |
| `ligerito_final`, `AcceptTail`, `not_DC_end` | **Done** (`FRSoundness4TailLig`), plus `tail_of_accept` (the body of 3.x's `finalLaw_of`). |
| The frame theorem at `FrontObl` | **Done**: `ks4_of_front` (`FR.Rev4.ks4_of` at `μ := T4.muT …`, `ε := εR`). |
| Asked by P4a and P4b in their RESULTs | **Done**: `zW`/`zBlk` (P4a); `Reads`, `card_frame`, `esc_msD_frame`, `frontLocal_of` (P4b; `FRSoundnessFront` Part A, new module `FRSoundness4TailFront`). |

**Checks:**
- **Build.** `lake build FR FRSoundness4TailFront`: green, 2,448 jobs (`logs/T4/build-final.log`).
  `FRSoundness4TailFront` imports the whole T4 chain.
- **Axioms** (`ax/AxT4.lean`, `logs/T4/axioms.log`): every one of the 1,247 constants of the 11
  modules uses only `propext`, `Classical.choice` and `Quot.sound`. No `sorryAx`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`):
  229 files, 0 findings (`source-rule.log`).
- **Dependency audit** (`scratch/DepsT4.lean`, `logs/T4/deps-t4.log`). For each of the 595 T4
  declarations, the audit follows the statement, and the value of each definition, through
  definitions. Only two reach a 3.x root (`fsItems`, `items`, `fsStarts`, `fsRanges`, `Kind`), and
  both are intended:
  - `tail_shift`, a control that compares T4's positions with 3.x's;
  - `ks4_of_front`, through `FR.OpImpl`: the shared verifier's `targetS : Kind → …`.

**Imports for `FR.lean`:** add `import FRSoundness4TailFront`. It pulls the other ten modules.

## 1. Method (journal §1)

1. **What is copied, and why.** The audit `logs/T4/deps.txt` was run before the port. A 3.x tail
   declaration is copied if its statement reaches a 3.x root:
   - 489 declarations are copied (`copy.txt`);
   - 195 are position-free and imported, not copied (`keep.txt`). These are `lin`/`bz`/`batch`,
     `bindL`, `mlDoom`, `msD`, `D2`'s readers `clR2`/`Chk2`, `CloseN`, `mleN`, `tabs`, the ε
     arithmetic, and similar.
2. **The port is mechanical** (`logs/T4/port/port.py` and `gen.sh`; patches in `patches/*.py`).
   - The modules are regenerated from the 3.x text.
   - Namespace `FR.Snd.T4`. Lean resolves the innermost namespace first, so a copy shadows its 3.x
     original, and the unchanged proofs read T4's copies and 3.x's algebra.
   - Renames:
     - positions: `phStart/fsStarts/fsItems/fsRanges/fsRnd/phOf/rangesOK → …4`;
     - kind: `kindOf → kindOfC`, `Kind → CKind`, `lvl → CKind.lv` (`lvOf κ.m`);
     - chains: `Matches/IsChain/chains/EscG/muG/muG_step_of/… → G.*` at `fsSeq4`;
     - case splits: `cases κ` → the six-kind `rcases`.
3. **The semantic deltas are patches**, marked `T4:` in the source:
   - **positions** from P1.0 on are `+14`:
     - `capPos_eq = [2, 344, 383, 410, 434]` and the `p1Start` table `[332, 375, 402, 426, 448]`;
     - `pfStart_eq = 468`;
     - `phOf_check`, `phOf_ge` and `rounds_check` at 482 items;
     - `phOf_examples`;
   - **the six-kind tables**: `mLog_eq` (m = 30/31/32: `17…5`, `18…6`, `19…7`) and `cap_check`;
   - **`lv31_ok`**: the m = 31 ladder meets `mca_ud_line`'s hypotheses. 3.x's `pcsLevels` covers
     only m = 30 and m = 32; `lv_eq_pcsLevels` is restated at `L30`/`L32`;
   - **`fs_eq4`**: two `dsimp`s where an unfolded `G.Matches` meets `fsItems4`.

   **The kind enters only through the ladder.** Every kind-dependent fact is `lvOf κ.m`, closed by
   cases over the six kinds.

## 2. What was built (`loc.py`, `logs/T4/loc.txt`)

| Module | total / code / thm | Ported from; content |
|---|---|---|
| `FRSoundness4TailStep` | 937 / 669 / 48 | `StepA` (`capPos`, `colOf`, `wordOf`), `StepB` (`StepObl`, **`step_epsD`**, `D3`, `RoundsPhase`), `StepC` (`RejOK`, `stepObl_compose`, `lvN/K/E`, `p2_*`, `lv31_ok`), `StepE` (`MsForm`, `esc_msD`, **`PhaseObl`**, **`kstate_step`**, `hfin_*`, `D2`) |
| `FRSoundness4TailTruths` | 466 / 272 / 21 | `Truths`: `farL`, `decodeL`, `sAt`, `mLog`, `truthP1/P2/P3/C`, `truthC_of`, … |
| `FRSoundness4TailHide` | 582 / 432 / 42 | `Hide`: `p1Start`, `DH`, `hide_obl`, `hide_step`, **`muT`**, **`muT_step`** |
| `FRSoundness4TailFold` | 506 / 352 / 34 | `Walk`, `Weights`, `Fold`, plus PIOP Parts A–B: `fF`, `msgOf_F`, `fTab_F`, `zW`, `zBlk`, `zBlk_elem`, `zBlk_bool` |
| `FRSoundness4Tail` | 211 / 135 / 33 | `Tail`: `cStart`, `p3S0`, `pfStart`, `Same`, `*_same`, `nrP` |
| `FRSoundness4TailD` | 314 / 197 / 24 | `TailD`: `FrontLocal`, `lvW/lvC`, `D1`, `DCi`, `DP2`, `DP3`, `DPf`, **`DT`**, `RejT`, position certificates |
| `FRSoundness4TailO` | 366 / 294 / 25 | `TailO`: `habs_*`, `single_*`, `rejT_ok` |
| `FRSoundness4TailM` | 319 / 261 / 21 | `TailM`: `hfin_P2/P3`, `DT_stab` |
| `FRSoundness4TailC` | 404 / 323 / 23 | `Compose`: `RejC`, `DkC`, **`FrontObl`**, `tailCls_check`, **`phaseObl_of`**, `FrontChainStab`, `chainStab_of`, **`muT_laws_of_front`** (new) |
| `FRSoundness4TailLig` | 610 / 423 / 39 | `LigFinal`: **`LigeritoOut`**, **`ligerito_final`**, `ligerito_final_of_walk`, **`AcceptTail`**, **`not_DC_end`**; new: **`tail_of_accept`**, **`ks4_of_front`**, `tail_shift`, `nrP_kind`, `muT_laws_false` |
| `FRSoundness4TailFront` | 128 / 74 / 16 | `Front` Part A: `Reads` (+ `mono/or/and/not/append/ext1/ext/stab/chain`), `reads_of_same`, **`card_frame`**, **`esc_msD_frame`**, `frontLocal_of`, `not_reads_length` (new) |
| **total** | 4,843 / 3,432 / 326 | (3.x tail: 6,632 / 4,666 / 458) |

**Not copied:**

| Declarations | Reason |
|---|---|
| `z3_*`, `lr2_phase`, `e2_phase` | The front's rounds phases; P4's. |
| `kindOf_P30`, `kindOf_default` | Replaced by S-G13's `kindOfC_ctrl`. |
| `truthP1_zero` | B′'s handoff. Unused downstream, and it needs PIOP's `truthB'`. |
| `stream_padded` | 3.x's node stream. Revision 4.1's padding is a claim of the node relation (R-4-m2). |
| `kstate_of_front`, `ks_of_front`, `finalLaw_of` | They target 3.x's verifier and `FinalLaw`. Replaced by `muT_laws_of_front`, `ks4_of_front` and `tail_of_accept`. |
| `Front` Parts B–D | 3.x's node layout and B′ cells; S-E's. |

## 3. The main statements (all in `FR.Snd.T4`)

```lean
structure FrontObl (RejF DF W₀ c₀) : Prop   -- form unchanged; positions at seq4 (p1Start 0 = 332)
theorem phaseObl_of (hFr : FrontObl RejF DF W₀ c₀) : PhaseObl (RejC RejF c₀) (DkC DF W₀ c₀) (239 * 2 ^ 128)
noncomputable def muT (Rej Dk) (L) : ℝ≥0 :=
  G.muG (DC Rej (Dp Dk)) (pRoundG (DC Rej (Dp Dk)) fsRnd4) L + G.muG DH (pRoundG DH fsRnd4) L
theorem muT_laws_of_front (hFr : FrontObl RejF DF W₀ c₀) :
    muT (RejC RejF c₀) (DkC DF W₀ c₀) [] = 0 ∧
    ∀ L q, L.length < logCap → muT (RejC RejF c₀) (DkC DF W₀ c₀) L < 1 → q ∉ L.map Prod.fst →
      ∑ a : Digest, muT … (L ++ [(q, a)]) ≤ (muT … L + epsR) * 2 ^ 256
theorem ligerito_final (hF : FrontLocal W₀ c₀) {L es} (hlen : p3S0 4 < es.length)
    (hD : ∀ p, p1Start 0 ≤ p → p < es.length → ¬ DT W₀ c₀ (phOf4 p) L (es.take (p + 1)))
    (hH : DH L es) : LigeritoOut W₀ c₀ L es
theorem not_DC_end (h : AcceptTail RejF W₀ c₀ L j) :
    ¬ DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀)) L (entriesOf L (pathOf L j))
theorem tail_of_accept (hF : FrontLocal W₀ c₀) (hFS : FrontChainStab RejF DF)
    (hμ : muT (RejC RejF c₀) (DkC DF W₀ c₀) L < 1) (hT : AcceptTail RejF W₀ c₀ L j) :
    (∀ p < (entriesOf L (pathOf L j)).length,
      ¬ DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀)) L ((entriesOf L (pathOf L j)).take (p + 1))) ∧
    LigeritoOut W₀ c₀ L (entriesOf L (pathOf L j))
theorem ks4_of_front (impl₀ implN cells S vk) (hV : S.V = Rev4.VC4 impl₀ implN cells)
    (hq : S.qV = Rev4.qV4) (hE : Rev4.ExtOff S.E) (hFr : FrontObl RejF DF W₀ c₀)
    (hS : Rev4.SegSoundLog (Rev4.VsegC impl₀) vk Good)
    (hN : Rev4.NodeExtLog (Rev4.VnodeC implN cells) vk Good S.E (Rel (S.acc vk))) :
    KS (Rel (S.acc vk)) (S.V vk) S.E epsR S.qV
  -- Good L := L.length ≤ logCap ∧ muT (RejC RejF c₀) (DkC DF W₀ c₀) L < 1
```

`step_epsD` and `hide_step` (the doom potential and the Hide potential) both come from
`G.muG_step_of fsRnd4_ok fsRnd4_zero`. `AcceptTail`'s fields are 3.x's at `seq4`:
- `chain`;
- `len : pfStart + 14 ≤ |chain|`, with `pfStart = 468`, so the bound is 482;
- `rejF`;
- `p1`: the `Chk2 (p1Start i) …` checks;
- `pf`;
- `lvl4 : truthP3 (kindOfC …) … 4`;
- `fin`: the Pf binding, with `∏ v ∈ Ico (mLog κ 4) 7`. `mLog κ 4` is 5, 6 or 7 for m = 30, 31, 32
  (`mLog4_le`).

## 4. What X4 should call

1. **The final theorem:**

   ```lean
   T4.ks4_of_front impl₀ implN cells S vk hV hq hE hFr hS hN
   ```

   Then `epsR_le_errorCap` (3.x `FRKState`, position-free) for the contract's cap.
   - `hFr : T4.FrontObl RejF DF W₀ c₀` is P4a's and P4b's: the front's phases 0–25, with
     `handoff` into **T4's** `D1 W₀ c₀ 0`. **P4 must target `FR.Snd.T4.FrontObl`.**
   - It also needs `FrontChainStab RejF DF` (P4's), for item 2.
2. **Inside `hS`/`hN`.** On `Good L` and an accepted run, R4 gives a chain `j` with
   `T4.AcceptTail RejF W₀ c₀ L j`. Then

   ```lean
   T4.tail_of_accept hFr.loc hFS hμ hT
   ```

   gives:
   - no composed doom on any prefix, from which P4's truths follow (Z/L/S, RS, B′; `SegHolds`);
   - `LigeritoOut`, with `LigeritoOut.claim0` and `level0_committed`: `c₀ = ⟨W₀, ι ∘ fF⟩` with
     `f⁽⁰⁾` fixed by the cap₀ commitment.

   `zW κ L es` (`= unpack f⁽⁰⁾`, `zBlk_bool`) is the witness the segment and node truths read.
3. **For P4.**
   - Use T4's `fF`, `zW`, `Same`, `FrontLocal`, `D2`/`D3` (`ans3` reads `kindOfC`, as P4a asks),
     `RejOK`, `MsForm`, `esc_msD`, `hfin_*`, `Reads`, `card_frame`, `esc_msD_frame` and
     `frontLocal_of`. Do not port them again.
   - P4b's `FSrc` at revision 4.1 is `T4.Same` with `T4.fF`.

## 5. Times (sequential: `taskset -c 0 lake env lean -DElab.async=false --profile`; `logs/T4/times.txt`, `prof-*.log`)

| Module | wall (import ≈ 3.5 s) | kernel (type checking) | max RSS |
|---|---|---|---|
| `FRSoundness4TailStep` | 17.6 s | 5.43 s (`p2_row_le_q`'s 30 ℚ certificates, `lv_eq_pcsLevels`) | 3.04 GB |
| `FRSoundness4TailTruths` | 9.3 s | 0.69 s | 2.82 GB |
| `FRSoundness4TailHide` | 15.5 s | 5.77 s (`cap_check`, `p1_sq_check`) | 3.16 GB |
| `FRSoundness4TailFold` | 11.1 s | 0.74 s | 2.82 GB |
| `FRSoundness4Tail` | 7.2 s | 0.39 s | 2.80 GB |
| `FRSoundness4TailD` | 18.4 s | 9.68 s (`phOf_check` over 482 positions, `rounds_check`) | 3.30 GB |
| `FRSoundness4TailO` | 11.2 s | 2.55 s | 2.97 GB |
| `FRSoundness4TailM` | 9.4 s | 1.25 s | 2.83 GB |
| `FRSoundness4TailC` | 16.3 s | 7.67 s (`tailCls_check`, `front_check`) | 3.03 GB |
| `FRSoundness4TailLig` | 18.8 s | 5.52 s | 2.99 GB |
| `FRSoundness4TailFront` | 8.7 s | 0.06 s | 2.84 GB |
| **total** | 143.5 s | 39.7 s | |

Every `decide` is a checked position or ladder certificate (`decide +kernel` over `fsStarts4`,
`fsItems4`, or the six ladders), as in 3.x. None runs over a program or a table.

## 6. Controls

**Copied from 3.x, now at `seq4`:**

| Control | Sign | What it shows |
|---|---|---|
| `phaseObl_false`, `frontObl_false`, `rejOK_false` | + | The obligations are satisfiable. |
| `not_rejOK_len` | − | `RejOK` refuses a length check. |
| `D2_first_absorb`, `D3_first_absorb` / `not_D2_before`, `not_D3_before` | + / − | The round dooms start at the phase's absorb. |
| `phOf_examples` | value | Phases 3, 4, 30 and 51 at positions 12, 13, 370 and 481. |
| `DH_seed` / `not_noHide_of_hideL`, `not_capOK_ext` | + / − | The Hide doom. |
| `not_farL_nil`, `foldAt_nil`, `not_hideL_of_univ`, `wordOf_nil` | | The empty-log values. |
| `closeP_nil`, `D1_of_far`, `not_D1_nil`, `p3T_zero`, `not_rejT_short` | | The tail dooms' edges. |
| `ligeritoOut_nil` / `not_ligeritoOut_one` | + / − | The claim field is not vacuous. |
| `not_acceptTail_of_cons` | − | `lvl4` is not vacuous. |
| `pfP_eq`, `ptL_four_lt`, `pf_round0_agree` | value | The readers. |
| `chainStab_const` | + | `ChainStab` holds for a constant predicate. |

**New (T4):**

| Control | Sign | What it shows |
|---|---|---|
| **`tail_shift`** | + / − | At every level, P1.i, C.i, P3.i's entry, the caps of levels 1–4 and Pf are 3.x's plus 14; `cap₀` is unchanged. So T4's positions are not 3.x's. |
| **`nrP_kind`** | ± | P1.0's rounds read the chain's `m`: 24 for `L31`/`N2`, 25 for `L32`/`N8`, 23 for `L30`. |
| **`mLog_eq`** | value | The six kinds' message logs. |
| **`lv31_ok`** | + | The m = 31 ladder meets `mca_ud_line`'s hypotheses. |
| **`muT_laws_false`** | + | `muT_laws_of_front` applies to a satisfiable front. |
| **`not_reads_length`** | − | `Reads` is not vacuous. |

## 7. Deviations

1. **Names.** S-G13 §6 asked for `muT4` and `PhaseObl4`. They are delivered as
   `FR.Snd.T4.muT` and `FR.Snd.T4.PhaseObl`: the brief allowed a `T4` namespace in place of
   prefixed names, and the namespace keeps the copied proofs unchanged.
2. **Scope additions.**
   - `fF`, `msgOf_F`, `fTab_F`, `zW`, `zBlk` (PIOP Parts A–B), because `LigeritoOut.claim0` reads
     `fF` and P4a needs `zW`.
   - `FRSoundnessFront` Part A, because P4b's RESULT expects it from T4.
   - Both are tail-level readers that no other track owns.
3. **3.x's final law is not ported.** `finalLaw_of`, `kstate_of_front` and `ks_of_front` are
   replaced by `tail_of_accept`, `muT_laws_of_front` and `ks4_of_front` on S-G13's frame.

## 8. Open questions

1. **Retiring 3.x (S-G13 F4).** T4 imports `FRSoundnessLigFinal` for the 195 position-free
   declarations in `logs/T4/keep.txt`. These sit inside 3.x modules, interleaved with
   position-dependent ones. To retire the 3.x chain, move them to a shared module first; `keep.txt`
   is the list. `FRSoundnessFront` is also 3.x; T4 copies its Part A.
2. **One copy each.** P4a and P4b should consume T4's `fF`/`zW`/`D2`/`D3`/`Reads`/frames instead of
   their own copies (§4.3). If they already copied any of them, the orchestrator should pick one.
3. **`FR.OpImpl.targetS : Kind → …`.** The shared verifier implementation type still takes 3.x's
   3-constructor `Kind`, as the audit shows. It is outside T4. Whoever owns the revision 4.1
   `targetS` (P4a's `targetSSeg`) should confirm that the Rev4 programs do not depend on it.
4. **`PhaseObl`'s single-squeeze bound `239 · 2^128`** (`N_le`) is 3.x's. The tail meets it. The
   front's rows at revision 4.1 (Lr 17, E2 23, E4 25) must also stay within 239 coordinates per
   squeeze. This is P4b's check (`coord_rows_le`).
