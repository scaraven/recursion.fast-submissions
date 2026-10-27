# S-E1 (track L-circ, first half): journal

Stage S-E, first half: the BLAKE2s circuit modules and the leaf circuit. Build tree
`logs/fr-build-circ` (copy of `logs/fr-build/gen.sh`), logs under `logs/S-E1/`.

## 2026-10-27

- Read TRACK-RULES, BLUEPRINT §4, §4.1, §4.2, §4.4, §7, §9, Appendix A.6, BP-C-M5 and BP-E-R2-M1.
- **Copied** the six BLAKE2s modules from `submissions/spartan-srom/lean/SpartanSromBlake2s*.lean`
  (branch at `783328c`), renamed to namespace `FR`:
  - `FRBlake2sCircuit`, `FRBlake2sWords`: unchanged.
  - `FRBlake2sCompress`: **re-based** to Appendix A.6 by changing the six layout constants only
    (`constPos` 512 → 1152, `msgBase` 640 → 512, `counterLo` 1152 → 1024, `counterHi` 1184 → 1056,
    `finalFlag` 1216 → 1088, `lastNodeFlag` 1248 → 1120) and the input set (`0…255`, `512…1151`).
    Gate positions (`1280…15999`) and the gadget order are leanVM's. Every proof went through
    with only the numerals in the range lemmas changed; the gates read input positions through
    `inW msgBase …`, so nothing else moved.
  - `FRBlake2sGeneric`: one range in `sim_compressW` changed.
  - `FRBlake2sWalk`: retargeted from spartan-srom's chain block (constant rows, row 512 skipped)
    to `blake2sCircuit` with every row, the constant's `(one, one)` row included
    (`walk_eq_sum` over all `k`; generic `rowOf_cpos`).
  - `FRBlake2sWitness`: `fastTrace inp` for any input block (was: for a chain digest);
    `blockAt`/`circuitRows` for `blake2sCircuit`; the IO dump functions dropped (a dump tool
    belongs outside `submissions/`, BLUEPRINT §8.1); `availAfter_getLsbD` moved here from
    spartan-srom's `R1CS` module.
- spartan-srom's `SpartanSromBlake2sR1CS` (the chain block with constant rows) is **not** copied:
  in this design the constants are public-pattern claims, so its content (h0, `leDigest`,
  `readDigest`, `block_getLsbD`, the one-block BLAKE2s lemma) moves to `FRBlockLayout`, and the
  chain-specific part is rewritten as a pattern in `FRBlockChain`.
- Observation (for the RESULT): with the constants on **input** positions (whose rows are
  `(var k, var one)`), any public pattern that pins an input bit to `1` forces `one = 1` through
  the R1CS (`z_k · z_one = z_k` with `z_k = 1`). The chain pattern pins `h_in = h0`, so for the
  leaf the `one = 1` hypothesis is implied by the chain pattern. The hypothesis is kept explicit
  in `leaf_sound` as asked (BP-C-M5), and a lemma shows the implication.
- `FRBlockLayout` (revision 2 form): readers, `compress_sound`, rows `rowOf_one/input/zero`,
  `zero_holds`, patterns. Trap: proving `rowOf k = ⟨0,0⟩` for the concrete `blake2sCircuit` hit
  "(kernel) deep recursion"; the generic lemma `rowOf_zero'` over any circuit, then instantiated,
  avoids it (the kernel otherwise unfolds the concrete circuit). Same pattern as `rowOf_cpos`.
- `FRBlockChain`, `FRBlockStream` (`blake2s_chain` by induction on `compressInput`, `stream_sound`
  by induction on blocks with `block_congr` for the message), `FRLeafCircuit`: built with
  patterns, one, links.

## Revision 3.1 (coordinator, mid-stage)

- Public target `E` replaces patterns. Rewrote: `Target`, `blockR1CS tgt` (circuit rows, `(0,0)` on
  the support), `targetVal`, `HoldsE`, `TargetOk`, `holdsE_sound/complete`, `zero_not_holdsE`,
  `walkE_eq_sum` (row weights masked on the support). The copied circuit stays the gate-level
  object (`circuitR1CS`); `holdsE_sound` reduces the target R1CS to it for Boolean blocks.
- Trap: `walkE_eq_sum` by `Finset.sum_congr` hit "maximum recursion depth" at elaboration
  (unifying sums over `Fin (2^14)`); rewriting with function equalities (`rw [hA, hB]`) works.
- `chainTarget` = old pattern + `one`; `streamTarget` = `t`, `f`, `one` only; `stream_sound` takes
  `hstart` (h_in(0) = h0) and `Padded` as hypotheses; `leaf_sound` takes `HoldsE` + `ChainLinks`.
  `one_of_input`, `leaf_sound_of_pattern` removed (moot).

## Revision 3.2 (coordinator)

- `blockTarget t fin` and `block_sound_gen` general in the counter and the final flag, so the
  node's `hashStmt` blocks `(41, final)`, `(64, ¬final)`, `(65, final)` instantiate it;
  `streamTarget L i := blockTarget (ctrAt L i) (i + 1 = nBlocks L)`.

## Final checks

- Clean build 74 s wall (lake parallel); kernel 28.3 s over the ten modules, 17.9 s for the six
  BLAKE2s modules (single core profile). Axioms: 40 declarations, standard three at most. Source
  rule: 0 findings. No name clash with the field modules (scratch import of all).

## Fix pass (revision 3.4, after review and golf)

- New `FRBlockKinds`: the `Kind` shape, the generic block lemmas, A.6's kinds (except `chain`,
  which stays `Chain.chainTarget`), one- and two-block hash lemmas, the `hashStmt` block lemmas, and
  the `kindRows` dump. Dropped an attempt to prove `chainKind.target = chainTarget` (the
  simp/split hit max recursion); the `chain` kind is `chainTarget` directly.
- Trap: `congr 2` on `compress … = compress …` with numerals (`64 * (0 + 1)`) hit max recursion
  and a whnf timeout; rewriting with `block_congr (l := …) (l' := …)` instead closes it.
- Sequential kernel time (`-DElab.async=false`): 7.9 s over the 11 modules.
