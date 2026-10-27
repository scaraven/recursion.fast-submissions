# S-0 (interfaces): journal

Running notes for a successor. Build tree `logs/fr-build-s0/` (`gen.sh` copied from `logs/fr-build/`,
`b.sh` from `logs/fr-build-piop/`). Logs under `logs/S-0/`.

## 2026-10-27

- Read TRACK-RULES, BLUEPRINT rev. 3 (`0d513c9`) §1–§3, §7, §9, §10, Appendix A; the contract's
  `Oracle.lean`, `Relation.lean`, `Certificate.lean`, `Signature.lean`; S-A's RESULT and field API;
  spartan-srom's `SpartanSromTranscript` (`idxOf`, `natLE`); the P1 prover's `transcript.rs`.
- **Design decision: one phase table.** `FRTranscriptDefs.phases` is a list of `Phase`s (name +
  `Shape`: seed / absorb / squeezes / uni / rounds / queries). `items` (A.4), the field sizes and
  `piSize` (A.3, `FRFormat`), `reassemble` (A.5) and `gen` (`FRVIR`) are all computed from it. The
  coordinator's heads-up (revision 3.1 coming) confirmed this: counts live in one place.
- `FRTranscriptDefs` built (rev. 3 numbers first: `items_length = 9007`, `streamBytes = 1,447,616`,
  `chainLen = 22,619`, all `decide +kernel`; plain `decide` hits `maxRecDepth`).
- `FRFormat`: `fieldSize` from the table, `piSize_eq` by `decide +kernel`; `parse_serialise` proved
  through `List.drop_sum_flatten` (the data of `serialise` is the flattened field lists).
- **`gen` design.** One op list for all kinds; kind-dependent data are tables `Kind → α` inside the
  ops (constants, assertion activity, dummy Merkle steps, position index maps); a `VProg` is a mode
  (`fixed κ` or `mux`) plus the ops. `gen (.fixed κ)` and `gen .mux` share the list literally.
  Asserts clear a flag and never stop the run, so every run asks every ask op (the item sequence is a
  constant). SSA registers, appended. `semIR` = the ops against a trace, consumed in order.
- Phase-final algebraic checks (Z's `Sẽl·Ê` check, Lc's walk, …) are **not** pinned by Appendix A in
  a form S-0 can write without guessing the PIOP; `gen` takes them as a parameter `fin : Finals`
  (ops appended after the skeleton). The skeleton has every query, every challenge map, every
  sumcheck round's consistency check, Z2's `lagrangeS`, every Merkle path and cap comparison, the
  column folds, the dummy-zero checks and the kind/statement checks.
- Revision 3.1 committed (`c38bda1`): 473 FS items, 8,896 items, `piSize = 756,496`, 16 fields,
  `Pf` added, L3/S3/I/B/R gone, `mbp` takes the point, `selMLE`/`targetMLE`/`shiftTarget` replace
  `rangeMLE`/`patMLE`. Adopted by editing the table (one place) and the op/impl list. The stream:
  1,440,336 B = 22,506 compressions (matches `sizes.txt`).
- Note: A.2 still says "the final message is 16 K-elements (512 B …)"; A.3 and §2.3 say `2^7` K
  (4,096 B). Taken A.3 (fix pass 3 is the later text).
- 14:12: S-A's golf pass is editing `FRField128.lean` (build broken upstream of S-0 for a while).
- Dump tool `probe/fr-irdump/` (lake project with the entry's modules as a library and a compiled
  `main`, no elaboration-time code): first summary 62,092 ops, 8,896 asks = `items` (checked by the
  executable as well as by `items_gen`).
- Revision 3.2 (`2709159`): `selWeight` replaces `selMLE`; `mbp r″ κ pt`; Z's final value. Added
  `finZ` (a `Finals` fragment) and `packFK` (a kind-dependent pack: P30 uses fewer coordinates).
- S-D's items: the framing already aligns every payload and answer (8-byte tag after `enc64`);
  proved `items_aligned`, `streamOff_aligned`; `parseNode`/`parseCol`/`carried` with the
  `MerkleEnc` laws (`parseNode_nodeQ`, `nodeQ_of_parseNode`, `parseCol_colQ`, `carried_nodeQ`,
  `carried_absorb`). Simp on `ByteArray.size` loops (`maxRecDepth`); rewrite with
  `Array.length_toList` instead.
- S-E1's items: `qlen_mod` (first query 119 ≡ 7, others ≡ 8 mod 16).
- FRVIRSpec generic layer proved: `runSeq_runIR`, `exec_append`, `queries_runIR`, `items_gen`,
  `queries_gen` (= 8,896, structural, no evaluation of `gen`), `semIR_mux`. Simp needs
  `List.filterMap_cons` explicitly to reduce `Op.item?` on op constructors.
- Phase Z lemmas in a scratch file first: the squeeze lemma by induction; the round lemma closes by
  `simp only [exec, evalOp, rd_app, …]` once the registers are kept in the form `r ++ L.toArray`
  (`push_app`, `app_app`); then `by_cases` on the two queries.
- Revision 3.3 (`1c1e27c`): `stmt` 128 B (the padded statement-hash blocks), `piSize = 756,560`,
  stream 1,440,400 B = 22,507 compressions; `carried` per query type (node, absorb, seed, squeeze)
  and `windows` (offsets ≡ 8 mod 16) for `inPlay`; A.6's eight block kinds and pinned intervals;
  `eqBits_eq_eq` (FRTranscriptDefs now imports FRRS and FRMLE); `domBits = 20`; ops `kindInd`,
  `maskRows` (concrete from A.6), `targetMLE r λ r′`, `walkA rowW colW`; `stmtOk` parses `stmt`.
- **Mid-point kill test (FR-R10), measured.** Phase Z (Z1 squeezes + 20 coordinates, Z2 univariate,
  Z3 26 degree-3 rounds, Zend absorb) is proved end to end (`exec_phaseZ`: Z's ops on any trace equal
  the reference `refZ`; no `sorry`). **364 code lines** (`loc.py`, scratch `z6.lean`, before
  golf), 25 declarations. × 15 phases = **5,460 lines against FRVIRSpec's 1,500 (3.6×)**: the
  rule as stated fails. Of the 364, ≈ 200 are shape lemmas reused by later phases (the interpreter
  steps, squeezes, absorb, degree-3 F rounds by induction, the univariate round); Z's own composite
  is ≈ 100. A shape-reuse projection for all phases is ≈ 2,000–2,300 lines (**estimate**): still
  over 1,500. Elaboration is slow-ish (the scratch file ≈ 48 s with everything before it).
  Proposal for the RESULT: re-budget FRVIRSpec to ≈ 2,500, or the fallback (`V` as structured Lean
  with `runIR (gen k) = V k` proved once).
- Revision 3.4 arrived mid-proof (L3 back as an absorb of 7 `v_kind` + squeeze β; E4 removed; 429
  FS items; `piSize = 755,568`; ops `kindFoldWeight`, `slotW`).
- Revision 3.4 adopted (table: L3 absorb 112 B into field 5 + squeeze β; E4 removed; ops `slotW`,
  `kindFoldWeight`). `exec_phaseZ` integrated into FRVIRSpec (Z's phase indices did not move).
- S-C had FRMLE mid-edit (uncommitted, failing) 15:19–15:23; built against a private source view
  `logs/fr-build-s0/src` (symlinks + the committed FRMLE) meanwhile; back on the entry sources once
  S-C committed (`d81b568`). The dump tool's `gen.sh` takes `SRC=` for the same situation.
- `exec_genPhase` stated over `refPhase` (shape references `roundsT`, `posAllT`, `seedT`, …): the
  one `sorry`.
- **Kernel trap**: `exec_round3` cost 36.9 s of kernel time. Bisected: `simp only [exec, evalOp]`
  alone is 29 ms; adding `push_app`/`app_app` (the register-array normal form) costs 36–48 s.
  Fix: `exec_app` (one op from `r ++ L.toArray`, the normal form inside the lemma) — 0.07 s; the
  module went from 64.8 s to 27.2 s wall, kernel 40.1 s to 3.1 s. Use `exec_app` for the other
  shapes.
- FRTranscriptDefs kernel 12.2 s → 8.1 s: `items_aligned` derived from `qlen_mod` by `omega`,
  `chainLen_eq` by rewriting `streamBytes_eq`.
- Dump regenerated from the entry: 61,753 ops, 53,088 registers, asks = items = 8,852; fields as
  A.3 (rev 3.4); `sizes.py` re-run agrees; `serial.py` written (11,854-line serial path, ≈ 356 s
  estimate).
- Final kill-test count in the module: phase Z section 373 code lines (RESULT §7).

## Fix pass (2026-10-27, after `40b2f81`)

- Rev 3.5/3.6 interfaces: RS0 `5 × 128` (stream 1,437,936, chain 22,468), `piSize 757,616`;
  `windowsFrom`/`inPlay` by stream offset; `linkW`; ops `eqPt`/`rowW`/`shiftEq` (imports);
  `Meets` per op; `frEnc`; FRRS/FRMLE dropped from FRTranscriptDefs.
- M3: `refPhases`, `exec_genPhases` by induction (context lemma stated), `exec_skeleton`.
- M1: FRVIRFinals. `pureRun` keeps registers as `r ++ L` (the exec_app normal form).
- **16:37 OOM, mine**: the scratch `flag_finSh` (51 ops) — proof motives quadratic in the register
  list via `getElem?_cons_succ`, plus `b + 16 + 4 + …` index chains. After the OOM every Lean call
  runs under `systemd-run --user --scope -p MemoryMax=12G/16G` (`logs/fr-build-s0/b.sh`, `cap.sh`).
  Fixes: closed-form register numbers in `hornerOps`/`linkOps`; generalise `phaseOff …` (its whnf
  evaluates the phase table) and every input register; lookups by `List.getD_cons_succ` (rfl
  lemmas). Kernel: finZ/finLc/finSh/finLr 0.4/0.4/0.36/0.08 s.
- `exact ⟨_, rfl⟩` closing a flag lemma times out whenever any `r.size + a + b` index or an
  unevaluated `if 1 = 0` is left: always look at the residual goal first.
- Rev 3.7: Lr-end/E-end absorbs (new fields 8 and 11; the rest renumbered), finLr from the Lr-end
  field, exec_phaseZ's simp needs `¬(fZend = fLrEnd ∨ fZend = fEEnd)`. Dump/sizes/serial re-run,
  all agree (8,854 items, piSize 757,712).
- 2026-10-27: last sorrys closed. Kernel "deep recursion" in exec_posOps = `rw` with `_` args solved
  by unification against a big goal; a closed lemma with explicit args fixes it. `omega` ignores
  `<` at `Reg` (abbrev): `dsimp only [Reg] at *`. A silent (no heartbeat error) multi-minute simp
  in flag_finSh = indices `r.size + 7 + k` from a `let b := b₀ + 7`: add `Nat.add_assoc`.
- Rev 3.9 ops landed (eqZ λ ρ₁, rsWeight/phiRS, evalMK, shiftTarget bnd); FRVIRCompile pattern
  touched (S-E2's, flagged). Dump: 149,974 ops with S-F's finals; items unchanged.
