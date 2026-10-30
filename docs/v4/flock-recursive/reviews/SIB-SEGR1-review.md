# Review: SIB (`648720f`) and SEG-R1 (`9a3019d`)

Cheap early review, read-only (no lake/lean run). Inputs: `git show` of both commits, `SIB-RESULT.md`,
`SEG-R1-RESULT.md`, the new modules, `logs/SIB*`, `logs/SEGR1*`. Paths below are relative to
`submissions/flock-recursive/lean/` unless stated.

**Verdict: no blocker. Both stages are sound as committed (every new claim is a theorem, and `certified`
still has the single hypothesis `Gaps4`). Before SEG-R2, fix two things: record honest acceptance after the
`evalM`/`evalL` pin, and choose a discharge route for `impQP` that does not make the kernel evaluate the compile.**

## Blockers

None.

## Should-fix

1. **Completeness after the pin is not measured.** `FRSegTarget4.lean:219-233` changes the segment
   verifier itself: `implSeg` pins `evalM`/`evalL` to `(0,0,0)`, and `specSeg` follows. This is sound,
   because `implSeg_meets` and the whole build still hold. Acceptance, however, now depends on the SEG-R0 §6
   claim that both ops feed only an `assertEq` that is inactive at every kind, and on nothing absorbing
   their outputs into the transcript. The only post-pin run, `logs/SEGR1/ab-segv.log` driven by
   `logs/SEGR1/ab.sh`, greps timings and throws away the verdict (`o.tmp` is deleted). Add a logged honest
   ACCEPT for each segment kind (L30/L32/P30/N30) and for N2/N4/N8 on HEAD, through `check.sh` or
   `plan4t check`, before R2 depends on it.

2. **Discharging `impQP` will need a cheap route.** `SlotRunC` (`FRNodeRun4CB.lean:223-227`) leaves
   `∀ i ∈ impQP rt A π, …`, where `impQP` (`FRNodeRun4CB.lean:133-142`) is defined through
   `stepOut`/`CS.add` along the whole compile of `protoProg π`. Showing that it is empty or small, which
   is SEG-R2's target "`impBP (rtC1d 1)` has no replay op", by `decide` or `rfl` means the kernel
   evaluates the full compile (≈ 26k ops, the templates' extension included). That is the kind of
   unfolding SIB took care to avoid. A failing row costs one row and no kernel work, so prefer it: make
   `isRep` ops that the replay template does not cover fail in the circuit. One way is a closure-style row
   with `rt.cov` passed into `askTG`. Another is the op-aware `inOk` that SEG-R1-RESULT §10.1 proposes for
   an `rsWeight` whose `act` is true. Then `impQP ⊆ []` follows structurally, as `impB_sub` does for the
   closure. This also settles SEG-R1's open question 1: an uncovered `rsWeight` would be rejected instead of
   left as an import (`FRNodeRows4RepSeg.lean:110-112`, `isRSS`).

3. **The docs point R2 at removed theorems.** SEG-R1-RESULT §7.2 (line 161) and `design/SEG-R.md:242` tell
   R2 to rewire `gaps4_of_runS`/`gap4Imp_rtC1c…S`, which SIB removed. R2 must rewire `gap4Imp_of_close` /
   `gap4Imp_rtC1cC` / `gaps4_of_runC` (`FRNodeRun4CT.lean:72,144,157`), changing the `rt` argument of
   `SlotRunC` from `rtC1c` to `rtC1d`. Also, SEG-R1-RESULT line 25 ("not imported by `FR.lean`") is stale:
   `9a3019d` adds the import. Fix these so that the R2 agent is not misled.

## Notes

1. **Is the closure total?** (`FRNodeRows4AskC.lean:155-156, 195-201`; `FRNodeRun4CB.lean:150-184,
   238-274`) Yes, by theorem rather than by inspection:
   - `impB_sub` proves that every residual import of the closed template is an `isRep` op's. The asks are
     excluded by `impBX`'s `item?` test and handled by `ATAsk`. A `bitOf` that is followed by its
     `selectHalf` is excluded by `bitNx`, and `bitNxAll` is forced by the failing row at the first ask
     (`first_ask`, l. 245-255).
   - Any foreign flag reaches `forRows`. This rests on `opOut_foreign`, which shows that a foreign flag
     implies `forCap`, and on `closeCov_of_forCap`.

   The `skip` set is therefore exactly {asks, `bitOf`+`selectHalf`, `isRep`}, and only `isRep` reaches
   `SlotRunC`. A sibling read whose `sibAt` is `none` is not `sibCov`. It falls to the closure as a
   `piDigest` (`opImp`, not `extCan`), so `impRows` fails it unless another class covers it. Good.
2. **`SlotRunC`'s residual matches the RESULT.** It has two conjuncts and no flag conjunct. The
   `hlen` of `slotRunB_of_close` is discharged in `gap4Imp_of_close` (`FRNodeRun4CT.lean:141`,
   `stepOut_len hX`). There is one imprecision in the wording: the first conjunct covers every aux with
   `isBitsA = false`, not "felems" by name. That matches the RESULT's 871 felems only if those are the only
   non-bits aux cells. Worth a one-line probe or a lemma when `colTG` is folded.
3. **The three removed theorems have no other users** among the `.lean` files. A grep finds them only in
   comments (`FRNodeRun4BT.lean:245`, `FRNodeRows4AskBS.lean:169` doc) and in docs (see should-fix 3).
4. **`sibAt`/`sibPosOk` reject; they are not skipped.** A failed check yields `[failRT P]`
   (`FRNodeRows4AskC.lean:65-76`) inside `askTG`'s rows. These fold into `nodeIRows4` by `rfl`
   (`askFold_close`), so no witness satisfies the circuit; `atImp_sib` uses exactly that (CS l. 84-85).
   The price is completeness, not soundness: the honest probe reports 0 failing rows (`sibstat-final.log`).
5. **SEG-R1: proved function vs. running function.** There is no gap. `implS := implSeg Impl.implC0`
   (`FRSubmission4V.lean:35`) is the compiled constant. `implS_eq` (l. 52) instantiates `implSeg_implC0`
   (l. 45), a `rfl` that is generic in the plans, so no plan is whnf'd. `VsegF_eq`/`VnodeF_eq`
   (l. 88, 93) rewrite through it, and `V4F_eq`'s statement is unchanged. `segBase_implB`
   (`FRNodeRows4RepSeg.lean:328`) is a projection `rfl` and does not force `nodePlan`. `Vnode4` becoming
   a `noncomputable abbrev` (`FRSubmission4Cert.lean:46`) is used only in Props. Compiled code that names
   `Sub4.implB`/`Impl.implCN` now fails to build rather than misbehaving, which is the safe direction. The
   orchestrator's combined build is green (`logs/SEGR1-orch-build.out`, 2,695 jobs).
6. **Pinning `evalM`/`evalL` is sound.** `rtEvZ_okW` needs no hypothesis because `implP … 1 ι` reads the
   pinned field by `rfl` (`FRNodeRows4RepSegK.lean` end). The only risk is completeness (should-fix 1).
7. **`cov`/`inOk` in `kRSS`.** A shape that `cov` (`isRSS`) misses stays an import and lands in the
   `impQP` residual (it is `isRep`), so it is never silently trusted. Bad operand types, a bad output
   shape and forms not below `B` all give `rejRow` (`kdRows`, `FRNodeRows4RepSegK.lean` `kdRows`'s
   `else`/`none` arms). `zf` forces `f₁ = 0` on the claims, and `rsWeightF_seg` uses it, so the
   F-point restriction is enforced and not assumed. The mux is sound under `SelOk` (`kdPos_ev`), and
   constant hints are justified by `kc_ev`/`zeroLin_ev`.
8. **Kernel time.**
   - `atImp_sib` takes 4.35 s of type checking (SIB-RESULT §5) and will be on `certified`'s path once
     `Gaps4` is routed. A likely cause is `cases op <;> simp only` over every `Op` constructor
     (`FRNodeRun4CS.lean:45`), or a defeq that reaches `itemsT`. Try matching `piDigest` first with
     `match op, hcv with | .piDigest f o, _ => …`.
   - `FRNodeRows4RepSegK` elaborates in 40 s, off-path until R2.
   - The `decide`s are all small: `isRSS_*`, `rssIn_*`, `byte_ne_zero`, `ofBytes_zero16`, and the
     `itAt_seed` byte index at `FRNodeRun4CD.lean:196`.
   - `askFold_close` is `rfl` at a variable `π`, so no table is unfolded.
   - No `decide` runs on closed tables in the new modules.
9. **Hard-rule words.** A grep of every new or touched `.lean` file finds no
   sorry/native_decide/partial/unsafe/opaque/implemented_by/extern/#eval/elab/macro/initialize/run_cmd/
   export/csimp/cpass/computed_field. The only hits for "init" are the identifiers `CS.init`/`St.init`.
   Both RESULTs log a source rule with 0 findings.
10. **Init cap.** SIB exceeds the +0.2 s init cap by +2.7 s (siblings' rows). SEG-R1's −2.05 s roughly
    offsets it. Under "acceptance over performance" this is acceptable; just record that the cap was waived.
