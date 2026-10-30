# FEL review (cheap early review of `design/FEL.md`)

Read-only review, 2026-10-30. Nothing built or run. Worktree `recursion.fast-submissions-rev44`, HEAD `9db5ee0` plus
SEG-R2's uncommitted edits. File:line refers to `submissions/flock-recursive/lean/` in the working tree, unless it
says HEAD.

**Verdict: the route is sound and is the right one. The memo's claim that the soundness chain is "unchanged" is
false, though (B1). The init-cost estimate contradicts the memo's own reference measurement (S1). Land it after
SEG-R2, preferably as the smaller "override the `dotKF` arm" variant (S3).**

## Blockers

**B1. The extension's soundness lemmas are stated at `L.ctx`, and FEL's `Xof` is not at `L.ctx`. The memo
says they are unchanged.**

- `tplExt_ok … (L : TLay) : ExtOk impl L.ctx (tplExt L.ctx)` (`FRVIRTplExt.lean:348`). The chain built on it is
  stated at the same context:
  - `tplExtF_ok` (`FRVIRTplSet.lean:144`, via `fixT`);
  - `tplExt4S_okAt … : ExtOkAt impl L.ctx (tplExt4S F R L.ctx)` (`:251–252`);
  - `tplExt4_okK` (`:535–537`);
  - `compileTF4_soundAt` (`:551–564`).
- FEL keeps `TLay.ctx`'s `col := none` (§3.1). In that context, `tplExt_ok`'s new alias branch is dead code.
- Meanwhile `Xof π := tplExt4 … (protoCtx π)` has `col := some (colA π)`. No lemma covers it.
- §3.3 says "`tplExt4S_okAt`/`tplExt4_okK` (`TplSet:251, 535`) unchanged". That is wrong.
- What follows:
  - All five lemmas need a context parameter, e.g. `TLay.ctxC L c := ⟨tplOf, L.cb, c⟩` with `L.ctx := L.ctxC
    none`. `instRows` reads only `tpl`/`cb`, so the proofs carry over. Every `tin_eqns (tc := L.ctx)` in
    `tplExt_ok`'s arms is retyped.
  - Six call sites that build the node's `ExtOkK` for `Xof π` must pass the alias:
    - `FRNodeRows4RepW.lean:65`, `FRNodeRun4BF.lean:214`, `FRNodeRun4BT.lean:213`, `FRNodeRun4CT.lean:98`,
      `FRNodeRun4S.lean:97`;
    - `FRVIRTpl4Bridge.lean:108` (`protoCS_soundAt`).
  - `hlen` (`stepOut … .slots.length = op.nOut`, `CB` `slotRunB_of_close`) comes from the same `ExtOk` and moves
    with it.
- None of these files is in §5's list. `RepW` and `CT` are SEG-R2 files.
- This does not break the route, and it changes no certificate statement. It does falsify "statements kept"
  for these intermediate lemmas, and P0/P2 would hit it first.
- Fix: add the five lemmas and six sites to §3.3/§5, or take S3, which avoids the chain.

## Should-fix

**S1. The init-cost claim (≤ +0.3 s) is not supported.**

- Per op, `colA` calls:
  - `provOf (pvP π)`. `pvP π = provLT 0 (protoProg π).ops` is not a let-bound value. `colA π col n` calls it
    inside the function body, so the compiled code is likely to recompute the ≈ 155 k-op walk per `dotKF`.
    That is 871 × 155 k steps per walk, unless the compiler hoists it, which it does not do reliably for a
    term that depends on `π`.
  - `winE` twice per window: once in `winsOk` and once in `colCell`. Each `winE` is 17 `pfLoc` calls, each
    a `find?` over `pSegs`.
- The memo's own reference, `logs/IMPC/impcinit.log:1–6`: adding `colTG`, which does the same `winsOk`/`winE`
  work plus trivial rows, costs +650–720 ms **per prototype per walk** (p0 745 → 1422 ms; p1 721 → 1374 ms).
- `colA` is evaluated in several walks, not once:
  - the compile behind `protoCS`;
  - `askRowsT`'s trail, through `XofT π`;
  - again through `Xa` in `impRows` at every `dotKF`, since the closure covers `dotKF`;
  - the plan walks (`trailMS` at `Plan.lean:632`, `planData4_rows`).
- Expect seconds, not 0.3 s.
- Fix:
  - give `colA` its `pv` as an argument, computed once, as `askTG` already does with `let pv := provLT 0 ops`
    (`FRNodeRows4.lean`, `askTG`) and as `TG.close` is documented to need ("computed once by the caller");
  - better, precompute a per-prototype alias table, register ↦ `Option (List Lin)`, once, and make
    `colA` a lookup. Prove the lookup against the `colCell` specification;
  - restate P3's threshold after that.

**S2. Two controls in §5 would evaluate `winE` on `seq4`'s tables in the kernel (closed-table `decide`).**

- `colA_ctl` is described as "a toy `pv` … gives two arena cells". `colA π` is hard-wired to `pvP π` and to
  `winE`, which reads `pSegs`/`itOffA`/`itemsA` over the whole `seq4`.
- So the control is either impossible as stated (no toy `pv` can be injected), or it is a `decide`/`rfl`
  over the real tables, which is the trap the memo itself warns about (§5, "no `decide` over `pvP`, `winE`").
- Fix: define a generic `colAW (pv) (win : ℕ → Option ℕ) (base : ℕ)`, with `colA π := colAW (pvP π) winE
  (π * slotM4 + arA1)`. Run the controls on a toy `pv` and a toy `win`. The literal `π * slotM4 + arA1 + e`
  that `PfCells` needs comes from instantiating `base`. Check that `Lin.ev_cell` then rewrites without
  unfolding `HAdd.hAdd` (the G5 hazard).

**S3. A smaller variant: override the `dotKF` arm at the `Xof` level and leave `TCtx` alone.**

- The memo's route adds a field to `FRVIRTplCore.TCtx`, close to the bottom of the import graph. That forces:
  - a full rebuild of every FR module, including all of SEG-R2's in-flight files;
  - the anonymous-constructor edits (12 controls in `TplSet:637–700`, `TplBuild:102`, `FRInitFuse`, `RepFD`,
    `RepCFP`, `AskPosT`);
  - the `isNone`/`tw`/`imp_tc` lemma changes in `CA`/`BF`/`AskBS`;
  - B1's chain of five lemmas.
- The memo's fallback, threading the alias as a parameter (≈ 70 edits), is no cheaper.
- A third option:
  - Define `tplExt4A F R tc al := fun P cs op => match op with | .dotKF w col => dkA F tc al P cs w col | _ =>
    tplExt4 F R tc P cs op`.
  - `dkA` is today's arm with `cells := al col n`, under `col < cs.slots.size` and the `F (.dotKF n)` filter
    that `tplExtF` applies. `tplExtKM`/`extGetK` never take `dotKF` (`AskIR:233–243`).
  - Set `Xof π := tplExt4A … (protoLay π).ctx (colA …)`, and the same for `XofT`, `Xa`, `XofA` and the plan
    walks.
- The soundness then needs:
  - one arm lemma, `dkA_okK`: a copy of `tplExt_ok`'s `dotKF` case (`FRVIRTplExt.lean:435–445`), which is
    already parametric in the cells, plus the `ImplTF F` step that `tplExtF_ok` uses;
  - a generic `orElse`-style split with the unchanged `tplExt4_okK`.
- `xofA_isNone` holds because `dkA` does not read `tc.tpl`.
- Untouched: `FRVIRTplCore`, `FRVIRTplExt`, `FRVIRTplSet`, `FRVIRTplBuild`, `FRInitFuse`, `RepCFP`, `AskPosT`,
  `CA`. That removes about 9 of the ≈ 20 modules and the B1 chain.
- What remains:
  - `Defs` (`Xof`, `colA`);
  - `FRNodeRows4` (`XofT`/`Xa`);
  - `AskBS` (`XofA`);
  - `CB` (`xofA_isNone`, `tplExt4A_isNone`);
  - the six `ExtOkK` sites, each with a one-term change to a single `xof_okK π ι` lemma;
  - `Plan`/`RepFD`/`RepCFW` (walk call sites);
  - `AskIR` (`xof_felems` + one arm);
  - the new `FRNodeRun4FE`.
- Cost: one duplicated ≈ 10-line arm proof.

**S4. Ordering: land FEL after SEG-R2, and after SEG-R1b, which SEG-R2 depends on (journal l.4–6).**

- FEL edits 7 of SEG-R2's 13 dirty files: `FRNodeRows4` (`askTG`'s `Xa`, `protoCS`), `Defs` (`Xof`), `Plan`
  (walk sites), `RepFD`, `CB`, `CT`, `RepW`. The last two come in through B1.
- FEL's §3.2 item 7 needs SEG-R2's (b) lemma in any case.
- The memo's line numbers are HEAD's, and SEG-R2 has moved them:
  - `SlotRunC` is `CB:223` at HEAD and `CB:291` now;
  - the Plan sites have shifted (e.g. `:619` → `:632`).
- Can run in parallel now, with no overlap:
  - the `FRNodeRows4Win` cut (it touches `AskI`, which SEG-R2 does not edit; keep names and namespaces so that
    `AskC`/`AskIR` are unaffected);
  - the Xof-independent lemmas `colA_some`/`aux_colA` (generic over `pv`, `win`, cells), in a new module above
    `AskIR`.
- Everything that changes `Xof` waits for SEG-R2's commit.

## Notes

**N1. Soundness of the binding: correct.**

- The register value and the arena cells meet in the same proof bytes:
  - `execA_prov` gives `regs[col] = .b (inp.π.extract (absOff f o) …)` for `provOf (pvP π) col = some
    (f,o,len)` (`AskIR:41–69`, `:71`);
  - `PfCells` gives `w (π*slotM4 + arA1 + e) = F.ofBytes (bytesAt inp.π o 16)` for `winE o = some e`
    (`AskIS:185–187`), in the same slot frame and the same `w` as the template's input forms. `aux_col`
    (`AskIR:183–221`) already uses exactly this frame with `a1Row`.
- `winsOk` forces `len % 16 = 0`. The `b ≥ len/16` branch yields `[]`, which evaluates to 0, matching
  `AuxK.val`'s `getD b 0` (`TplCore:348–350`).
- `colA` returns `List.range n` cells, so the lengths agree with `hc`'s map.
- In the honest program the column register is the preceding `piField`'s (`FRVIR.lean:832`: `.piField … (b+1)`,
  `.dotKF w (b+1)`).
- `tplExt_ok`'s `dotKF` case uses the aux cells only through `hc` (`FRVIRTplExt.lean:441–445`). The alias
  branch therefore needs no new reasoning; it needs only the B1 retyping.

**N2. A refused `dotKF` fails, and is not imported silently: confirmed.**

- `closeCov (.dotKF ..) = true` (`opImp`, `AskC:107–113`; `closeCov` `:155`).
- No component of `askTG` covers `dotKF`:
  - `impcCov` (`AskI:210–216`) does not;
  - `askTGT`/`inpTG`/`rsvTG`/`bitTG*`/`sibTG` do not mention it (grep);
  - `colTG` (`AskI:232–233`), the only `isDotKF` cover, is not folded;
  - `TG.repF` covers only `isRep` ops (`AskC:207–209`).
- So the closure takes the `impRows` branch: `extCan (.dotKF ..) = true` (`:173`), and the closure emits
  `failRT` iff `Xa` is `none` (`:179`).
- That requires `Xa`/`XofA` to refuse exactly where `Xof` does. The memo requires `col` in both (§3.1). Under S3
  they are the same wrapper over the template-free context.
- `impB_sub` (`CB:218–`) then leaves only `isRep` imports in the residual.

**N3. Recursion depth / R1: no issue.**

- No op, public input or recompute is added, so R-OPS "Superseded" (`R-OPS.md:323–338`) does not apply.
- In a grandparent's slot 0, prototype 0's `dotKF` aliases slot 0's own arena₁. `pfCells_of_rows` holds there
  as at any active slot (`AskIS:195–201`).
- A refused `dotKF` becomes an import only together with a `failRT`, so there is no free import at any depth.

**N4. Cost fidelity, other than S1.**

- **0 rows / 0 new cells / no `Gaps4`, `SlotRunC` or `certified` change: correct.** The old aux cells stay
  allocated and unreferenced. They do not clash with SEG-R2's new local bands (`segCell`, `Defs` diff), which
  were chosen against the unchanged layout.
- **"No V change":** a hope, not a fact. The instance inputs become scattered arena cells, or `[]`. P5 guards
  it. Keep it a measurement in the RESULT.
- **Kernel < 3 s: plausible.** No existing proof `decide`s or `rfl`s over `protoCS`/`pvP`/`winE` (grep), and
  `protoCS_X` stays `rfl` by unfolding. The `split`-heavy `tplExt_*` lemmas grow only under the memo's route,
  not under S3.

**N5. Plan / prover consistency.**

- Every walk that rebuilds a prototype's compile must use the aliasing extension:
  - `protoCS`, `XofT`, `Xa`, `XofA`;
  - `trailMS` (`Plan:632`), `planData4_rows`, `RepFD:51,64`, `RepCFW:152`, `RepCFP:362`;
  - the dev probes.
- A missed site does not threaten soundness. It does produce a plan whose `dotKF` inputs differ from the
  certified compile, and only `plan4t check`/MxKat (P5) would catch that.
- Add a P1 line that compares the `tin` of `protoCS π` with the plan walk's, instance by instance.
- `mfill`'s "already-set equal cell" change is a real prover edit. List it in §5's file list.

**N6. Statement scope.** "No certificate statement change" holds. Intermediate statements do change:
`tplExt4_imp_tc` gains `hcol`, plus B1's chain. Keep them under the spec-authoring rule: generalised, not
weakened.
