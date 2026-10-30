# FEL implementation review (cheap, read-only)

Scope: the frozen copy `logs/FEL-orch-copy/*.lean`, compared with `git show HEAD:submissions/flock-recursive/lean/<file>`
(HEAD `b777e1a`), and `logs/FEL-orch-copy/docs/FEL-RESULT.md`. Design `design/FEL.md`, prior review `reviews/FEL-review.md`.
Nothing was built or run. Line numbers refer to the frozen copy.

**Verdict: sound. `certified` is the challenge's exact statement with no hypothesis, and the alias cannot cost
soundness. No blocker. One should-fix: get the end-to-end harness measurement (kernel replay and build time) before
calling the stage done.**

## 1. `Solution.lean`

- The diff against HEAD touches only the header comment (l.6–9) and `certified` (l.29–31). The imports (l.11–12),
  namespace and `open`s (l.14–16), `declared` (l.20–24) and `submission` (l.27) are byte-identical to HEAD.
- `certified` (l.30), `theorem certified : CertificateR declared submission`, and its docstring (l.29) match the
  stub `logs/org20/harness/challenge/Challenge.lean.in` l.26–27 character for character. `declared` matches the
  stub with the claim's values filled in, and these values are unchanged from HEAD.
- The proof is `certificateR_sub4F declared boundsOK_claim open4F_holds` (l.31). `open4F_holds : Open4F :=
  N4s.gaps4_fel` (`FRSubmission4Fin` l.43). `Open4F`, `Gaps4` and `certificateR_sub4F` are unchanged at HEAD.
  `logs/FEL/axioms.log` l.31 gives `[propext, Classical.choice, Quot.sound]`.

## 2. Soundness of the alias

- **A missing column is refused.** `colA π col n` (`Defs` l.219–220) is a `List.lookup` and returns `none` when
  the column is not in the table. `dkA` (`FRVIRTplAlias` l.26–34) maps `none` to `none`, so `Xof` takes no
  template. `stepOut` then falls back to `opOut`, which marks the op as an import because `opImp (.dotKF ..) =
  true` (`FRNodeRows4AskC` l.111). The closure emits `impRows`'s `[failRT P]` (`AskC` l.179–180) whenever
  `(X P cs op).isNone`. The closure's extension `askTG`'s `Xa = XofC π ⟨empty, cb⟩` (`FRNodeRows4` l.241) refuses
  exactly the same ops as the compile's (`dkA_isNone`, `tplExt4A_isNone`, `CA` l.124–132). A refused op can
  therefore never get unbound cells: `felems` entries come only from `dkA` (`xof_felemsA`, `FE` l.148–167).
- **The tables affect only compile decisions.** Soundness never depends on what the tables contain:
  - `colTab_lookup` and `esCache_lookup` (`FE` l.28–57) are proved by structural recursion on any column list.
    Every entry present is `colEWC …` (respectively `colEs …` at its own key).
  - `colTP_lookup` (l.75–87) unfolds `esC0`, `colT0` and `colT1` only by delta, with `cols :=` given explicitly.
  - `colA_some` (l.91–102) yields the specification form `provOf … = some (f,o,len) ∧ colEs … = some es ∧ cells =
    colCells …`. `felems_of_pf` (l.171–187) then discharges each `felems` fact from `PfCells`, `execA_prov` and
    `aux_colW`, which is generic in `win` and `base`.

  A wrong or short table can only refuse more ops. That makes the closure fail an honest run, so it costs
  completeness only.
- **The arm is sound for any `al`.** `tplExt4A_okK` (`Alias` l.110–118) quantifies over `al`, and `dkX_ok` uses the
  cells only through the auxiliary hypothesis `hx` (l.91–94). The whole obligation therefore sits on the aux fact,
  which `felems_of_pf` proves. Every `ExtOkK` site (`RepW` l.66, `BF` l.218, `BT` l.214, `CT` l.99, `S` l.98,
  `Tpl4Bridge` l.108) passes `colA (protoOf κ v)` / `colA π`, which closes prior review B1.
- **The prototype-1 cache creates no aliasing hazard.** The cache key is `(absOff f o, len)`, and `colEs` depends
  only on `(winE, piSizeOf seq4, x, len)`, which are global and the same for both prototypes. `colEWC_eq` (l.60–68)
  shows that the cache is transparent, `hca` uses the same `sz` that `esC0` was built with, and `pvP_of_ne` covers
  π ≥ 1. Several `dotKF`s, or the arena write itself, sharing one arena₁ cell is harmless: each such cell is pinned
  to a fixed proof-byte value by `PfCells`, and `dkX_ok` needs no freshness.
- **Lengths.** `colCells base n es` always has `n` entries, with the zero form past `len/16`. `aux_colW` (l.108–143)
  proves equality with `AuxK.felems n` for every `n`, so `n` and `len/16` do not need to agree.

## 3. Generalised lemmas

`ExtFl X` (`CA` l.108) is exactly the old `tplExt4_flags` conclusion, abstracted over the extension.

- `stepOut_imp_of` and `stepOut_foreign_of` (`CA` l.135–148) have the same conclusions, now for any `X` with
  `ExtFl X`. The old forms follow through `extFl_tplExt4`.
- `atImp_close`, `atOk_close` (`CB` l.81, l.95) and `impB_sub` (`CB` l.217–221) replace the equation
  `X = tplExt4 F R tc` with the weaker `ExtFl X` and keep their conclusions.
- These are proof-help lemmas. None of them is on the statement side of `certified`, and no statement on
  `certified`'s side was weakened.
- Changed definitions: `protoCS`, `Xof`/`XofT`/`XofA`, `planData4`/`arOf`/…, and `repRowsP_trail`'s right side.
  Each change sits inside the submission. The verifier's circuit changes with them, and the certificate is
  re-proved for the new circuit.

## 4. Kernel hazards and hard-rule words

- **No closed-table evaluation in the kernel.**
  - No proof applies `decide`, `rfl` or `simp` to `esC0`, `colT0`, `colT1`, `winE`, `piSizeOf seq4` or a compile
    result.
  - The FE controls (l.207–222) and `dkA_ctl` (`Alias` l.131–140) are `rfl` on toy inputs only (S2 closed).
  - `xof_dk` (`Defs` l.232) is a `rfl` by delta.
  - `planData4_rows` now ends in `by rw [one_mul]; rfl` (`Plan` l.74). That `rfl` identifies `compileX (Xof π) …`
    with `compileX (XofC π (protoLay π).ctx) …`, which share a head, so the arguments are unified by unfolding
    `Xof`, a delta step. The measured `Plan` type checking time moved only from 1.57 to 1.73 s
    (`logs/FEL/prof-summary.txt`).
  - The `decide`s in the copy (`AskIR` l.129, l.447; `Model` l.74–93; `RepFD` l.94; `RepW` l.51; `CB` l.156) are
    unchanged from HEAD and involve small constants.
- **No hard-rule words.**
  - None of `native_decide`, `partial`, `unsafe`, `opaque`, `implemented_by`, `extern`, `#eval`, `elab`, `macro`,
    `initialize`, `run_cmd`, `export`, `csimp` or `import Lean` appears in the 24 files, comments included.
  - `sorry` appears only in a prose comment (`Solution` l.9, "contains no `sorry`"), as at HEAD. The source rule
    passes: `logs/FEL/source-rule.log`, 482 files, 0 findings.
  - The only attributes are `@[noinline]` (`Defs` l.423) and `@[inline]` (`Plan` l.1203). Neither changes code,
    and both were at HEAD.

## Findings

### Blockers

None.

### Should-fix

**FEL-I-S1. The cap figures are summed per-module profiles, not a harness run.** The ≈ 420 s of 600 s (RESULT §6)
adds `--profile` type-checking times to SEG-R2's ≈ 390 s. Closing `Gaps4` adds 40 modules to `certified`'s closure
(332 → 372) and ≈ 607 s of single-core elaboration (RESULT §6, open question 1). Neither the harness's
kernel-replay time nor its `build_s` against the caps has been measured. Run the entry pipeline end to end on the
FEL tree (certificate build plus kernel replay; `HARNESS: ACCEPT` is the stage's done criterion anyway) and quote
the log. Close this only with that measured figure.

### Notes

- **N1.** RESULT §2 lists symbols that are dead after FEL and kept: `colTG`, `colRows`, `auxRows`, `colOk`,
  `aux_col`, `SlotRunI`, `slotRunA_of_impc`, `withImpcC`, `askTGIC`, and `compileTF4` at the prototypes. They are
  for golf to retire. If any of them is in `certified`'s closure, removing it also trims kernel time.
- **N2.** `plan4t init` is +0.29 s (median), at the kill line. Under "acceptance over performance" this is not
  blocking. The `pfLoc` memo is the lever if the cap binds.
- **N3.** Prover re-dump (RESULT §7): `maux`, `plan-form` and the blob change, and `mfill` will write the aliased
  arena₁ cells twice with equal values. The honest node ACCEPT stays unmeasured until E1b re-dumps. This is
  completeness-side only.
- **N4.** The `Defs` section docstring (l.147–150) points to `FRNodeRows4AskC.impRows` for the refusal → failRT
  path. That is correct, and it is the right reference for a reader checking N2 of the prior review.
