# S-E3 journal (track L-circ: replay templates)

2026-10-27/28, branch `v4/flock-recursive`, started on `eba6537` (BLUEPRINT revision 3.11). Build
trees `logs/fr-build-e3` (later the subagent's) and `logs/fr-build-e3b` (`snap.sh`: HEAD's
versions of other tracks' modules, L-circ's files and the split `FRVerifierImpl*` as symlinks).
Every `lake`/probe run under `systemd-run --user --scope -p MemoryMax=16G -p MemorySwapMax=0`.

## Design decisions

- **Templates are a small arithmetic DSL** (`FRVIRTplCore`): wires `one` / `inp i` / `loc k`,
  product and inverse gates, outputs as linear forms. A generic lemma (`Tpl.eqns_of_rows`) turns
  "the rows hold" into "every gate equation holds", proved once. Each op's template mirrors its
  `implC` implementation gate for gate, so its correctness (`tplX_ok`) is a statement about pure
  functions with no `exec` reasoning.
- **The compiler gets a hook** (`Ext`, `compileFromX`) instead of a second compiler. Templated ops
  record an instance `(key, number, input forms)`. Their rows are *defined* as the expansion
  (`Tpl.instRows`), so the evaluator's rows and the soundness rows are the same object.
  `compile_sound` is re-derived from `compileX_sound` at `noExt`.
- **Soundness does not depend on the layout**: overlapping instance regions only add
  constraints. The layout is a two-pass compile (count, then lay out aligned groups).
- **MLE**: `tpl_mle` is the closed form of one aligned instance (`eq` split at bit `a` for rows and
  at bit `b` for cells), generic over a commutative ring `R` with `ι : F →+* R`, so that `evalM`
  (F) and `evalMK` (K) share it.

## Events

- The compiler took **12.5 s per slot**. `CS.add` read `cs.slots.size` after building the appended
  array, so `cs` stayed live and every append copied the slot array (O(n²)). With let-bound fields
  and the array last, it takes 0.15 s per pass (`logs/S-E3/` bench).
- The first evaluator run hung. `splitE m s t : ℕ → R` was eta-expanded by the compiler, so its two
  tables were rebuilt on every lookup. Fixed by passing the tables to `splitAt` (a PAP over arrays)
  and, in `prepOf`, `getD0 tbl`.
- `rfl` and `simp` steps that let the elaborator unfold `Impl.chainTab` (2^14 entries) or
  `pinnedRho` timed out at `whnf`. Fixed by stating the `targetS` template over arbitrary constants
  (`tgtT pr cf`) and instantiating.
- Coordinator items: (S-G1e) the six padding cells were dropped from `pubCells`/`pubVals`, and
  "partial" was reworded in a comment; (S-G1h) the WOTS order was exported (`wotsKindAt`,
  `ind_wots`); `RowsFit (nodeRows fin) 21 23`: see the RESULT (§ open).
- One subagent wrote the Lagrange-family, `eqTableK` and `dotKF` templates (`FRVIRTplLag`) in
  parallel, in its own build tree.
