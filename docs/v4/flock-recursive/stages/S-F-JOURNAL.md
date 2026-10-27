# S-F journal (track L-cert: the verifier)

- Read TRACK-RULES, BLUEPRINT rev 3.7 §3, §5.5–5.6, §7, A.8, A.9, §10 changes 1–5; S-0 and S-E2
  RESULTs; `FRVIR`, `FRVIRFinals`, `FRFormat`, `FRRingSwitch` (RS1 form `rsT`, `rs_column`,
  `quirky_claim_split`), the library's `WitnessSending`, spartan-srom's `accWith`/`V`.
- Build tree `logs/fr-build-cert` (copy of `fr-build-circ`'s `.lake`, `snap.sh` with other tracks'
  modules from HEAD, mine symlinked; `build.sh` filters errors). Every build in the 16 GB scope.
- Decided: S-F's fields in a new module `FRVIRFinalsSF` (S-G may edit `FRVIRFinals` concurrently).
- `finRS` design: `α_j` computed from the partials with low weights (`rs_column`), `v_RS` as
  `Σ_j κ^j T_j`, `T_j = Σ_i bitBasis i · Φ(s_{j,i})` (FRRingSwitch's `rsT`; A.9's
  `Σ eq(r″,u) s_u` does not match `rs1_joint` or `mbp`). Φ costs 127 squarings + 7 stages per
  partial: ≈ 70 k `mulF` in `gen` (reported).
- Proof kit: `pureRun_append`, `pr_op`, `pr_app'`, `rdX`, `rdL`; blocks `sqOps`, `phiOps` (value
  `frobMap (stages s …)`), `elemOps`/`elemsOps` (sums over `Finset.range`), `prodOps`/`lagAll`
  (Z's Lagrange weights), `claimOps`, `rsTail`; all by induction on the generators.
- Pitfall: `omega` fails silently on `<` at type `Reg` (an abbrev of ℕ): lemma binders as ℕ.
- `exec_finRS` proved for 5 claims; then the coordinator's message (rev 3.8): `J_z = 4`, Z's
  quirky point claim first, one Sh claim. Adapted: 4 claims (Z, Lc, Sh, Lr), `nRS = 4`, leaf's
  4th claim zero; `zLow` (Z1's first coordinate) isolated as one definition (open for S-0).
- `finE`, `finB′` and their flags in S-0's style (`simp` + `rfl` on short op lists).
- `FRVerifier`: `Vwith` by well-founded recursion, `accWith`, `accV`, `acc_eq`, `V_W`,
  `V_W_sound`, `complete` (`P := encodeF`, δ = 0), `exec_length`/`runSeq_length`, four controls.
- Source rule: the word "partial" in two docstrings fixed. Axioms: the three standard ones.
