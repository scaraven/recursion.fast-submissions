# X4 JOURNAL: composing revision 4.1's knowledge soundness

- Base: HEAD `bb5d352` (R4g). Build tree `logs/fr-build-X4` (copy of `fr-build-R4g`, `b.sh` logs to
  `logs/X4/`). 16G scope, `timeout`, no sub-agents, no commits.

## §0 Survey (before any proof)

- **T4** gives `ks4_of_front` (`KS … epsR` from `FrontObl RejF DF W₀ c₀`, `SegSoundLog`,
  `NodeExtLog` at `Good := len ≤ logCap ∧ muT … < 1`), `tail_of_accept` (needs `FrontLocal`,
  `FrontChainStab`, `AcceptTail`), `muT_laws_of_front`.
- **S-H2/S-H3** give `ks4_E4X` (`KS … ε` at `S.E = E4X nd S.acc`), with `NodeDec4 nd` and the links
  `hL` and `NodeSoundLog` as inputs.
- **P4a** (passes 4–5) gives phases 0 … 12 completely: `DF4a`, `RejF4a`, `ms4a`, `habs4a`,
  `hsingle4a`, `hfin4a`, `hstab4a`, `df_ss4a`, `front4`, `front4_ok`, `stmt_split4`, `sNode4`.
- **P4b** gives the 13 … 25 *units* (`lr4_*`, `e4_*`, `habs_RS0_4`, `rs1_hfin4`, `single_B4`, the
  readers `W₀L4`/`c₀L4`, `frontLocal4`) but **not** the composed phase dooms 13 … 25 nor their
  `FrontObl` obligations: P4b's own handover item 2 ("DF/Obl/Stab at phases 13–25") was never run.
  No `FSrc` instance at revision 4.1 exists either (P4b left `FSrc` a parameter).
- **R4** gives `acceptTail4_of_run` (with `¬ RejF` and `FinRest4` asked per accepted trace),
  `finRest4_of_fields` (leaves `pf0`, `enc`, `fin`: R4h), the `not_rej*` per check and kind.
- **S-E** gives `hfit4 : HFit4 nodeIRows4` (proved), `node_sound4`, `NodeResid4`; INT-9 gives
  `implN4F`, `srcE4`, `srcL4`, `implN4F_hM/_hL`.

## §1 Decisions

- D1. **The composed front** `DF k := if k ≤ 12 then DF4a P k else DFhi k` with `DFhi` a parameter, and
  `RejF := RejF4a M ∨ RejF4b` with `RejF4b` **concrete** (P4b's five checks, the ones R4 refutes).
  The obligations at positions < 170 / phases ≤ 12 are discharged by P4a's lemmas; those at positions
  ≥ 170 / phases 13 … 25 are one named residual `FrontHi` (P4b's unrun item 2), stated over the
  *composed* `DF`/`RejF` so that the boundary at 170 (`DF 13 = msD (DF 12) …`) is in it.
- D2. `FSrc` at 4.1: `src4` (T4's `Same`, `fF` at the log's kind), as 3.x's `src3`.
- D3. `BgA := far₀ ∨ ¬ PubOK4 ∨ RowsBadLr4 ∨ nE4` at INT-9's `srcL4`/`srcE4` and `cells4`
  (3.x's `far0 ∨ nPub ∨ nLr ∨ nE`); `NodeRest4 → BgA` by O1 (`sat_ofRows_iff` with the L rows' fit,
  `sat_entMatI_iff` with `hfit4`) and `pubL = pubVals ∘ pvL`.
- D4. `FrontHi` is stated over the *composed* `DFX`/`RejFX` (not over `DFhi` alone) for the fields
  that cross 170 (`ms` at `s0 + 1 = 170`, `habs` at 170, `hsingle`, `hfin`, `handoff`), so the
  owner of phases 13 … 25 meets exactly T4's obligations; `hstab`/`chain` are over `DFhi` at 13 … 25.
- D5. `hfin` below 170 is not `hfin4a` (whose `condCount` is over `DF4a`): `z1_hfin4`/`s1_hfin4`
  are called at `Dk := DFX DFhi` with `DFX_lo` rewrites (they are generic in `Dk`).
- D6. The laws use the **three-entry prefix**: `tail_of_accept`'s `¬ DC` at `p = 2` is
  `¬ DF4a P4X 2` on `es.take 3`, hence `Stmt4` there (`stmt_split4X`), and `chainEnd_of_truths`
  applies to `es.take 3` directly (its statement bytes, kind and `nStmt` read entries 0 and 1).
- D7. What R4 has not yet assembled is one residual `RunFacts4` (per accepted run: an
  `AcceptTail` of the composed front and the log's statement reads, `SegLog`/`NodeLog`).

## §2 Log

1. `FRSoundness4XFront`: `src4`, `BgA4`, `bgA4_reads`, `lRows4_fit`, `bgA4_cover`, `P4X`,
   `stmt_split4X`, `okX`, `okReads_X` (needed for `rejRS4_log`; never instantiated before),
   `RejF4b`, `RejFX`, `rejOK_X`, `ss_rejFX`, `DFX`, `W0X`, `c0X`, `FrontHi`, `frontObl_X`,
   `frontChainStab_X`. Elaborated first try except: `oSh4`'s congruence (needed `lastBits`,
   `nStmt_congr`), `open Classical in` before the docstring, a three-level `.inl`.
2. Kernel: `lRows4_fit`'s `decide +kernel` on the closed layout constants cost 3 × 2.4 s
   (`chainLenOf seq4` inside `hUsed`); replaced by `regions_fit`/`lSlots_fit`/`mSlots_fit` and
   `omega`: module kernel 7.6 s → 0.39 s.
3. `FRSoundness4XLaws`: `GoodX`, `SegLog`, `NodeLog`, `RunFacts4`, `agree_take3`,
   `stmt4_of_tail`, `segSound_X`, `nodeRun_X`.
4. `FRSoundness4XFinal`: `nodeSound_X` (via `nodeLaws4C'`), `ks_rev4` (via `ks4_E4X`),
   `Resid4`, `certificate_rev4`. `FRSoundness4XCtrl`: controls.
5. Checks: `lake build FR FRSoundness4XCtrl` green (2,533 jobs), axioms (16 names), source rule
   (313 files, 0 findings), sequential profiles.
