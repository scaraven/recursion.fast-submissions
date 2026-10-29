# R1 journal

- 2026-10-29: Read R-OPS, the review, R0, RSV-V2, IMP, and the code: `FRVIRFinals4` (`rsvEOps`, `gFinE`, `rsvBOps`,
  `gFinPf`), `FRVIR` (`Op`, `evalOp`, `uniTail`), `FRVIRCompile` (imports), `FRVIRTplLag`,
  `FRVerifierImplNode4F`. Copied `fr-build-IMP` to `fr-build-R1`.
- `tdot` design notes, now moot. Without changing `lagrangeS`, `tdot pt λ` equals
  `(impl.lagrangeS 0₁₂₇ λ (impl.targetS κ pt)).1`. In `uniTail4`, `lagrangeS` would have been fed
  `packF []`, whose template is `tplLagrangeS 127 0` (generic in `m`, no new proof), followed by an
  `addF`.
- Orchestrator: accepted beats fast, and the plain 168 variant is allowed. I chose plain 168: no pads, row 238.
- **Blocker found while laying out `rsvOps2`.** The child-check calls of V(P) (`evalL`, `targetS`,
  `linkWAll` on the child's carried data) have no template. They become imports of the
  grandparent's slot 0 (`impRP` covers every un-templated op of `protoProg 0`, and the compile
  routes those ops to `imports`). Binding them regresses with depth. RSV2 escapes this because its
  single stacked `evalM` is a sumcheck fixed point. Stopped. Details and the ways out are in
  `R1-RESULT.md`.
