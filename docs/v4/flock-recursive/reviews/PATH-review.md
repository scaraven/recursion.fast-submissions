# PATH review: the remaining path to `HARNESS: ACCEPT` (friction review, 2026-10-29)

Scope: a quick friction review, not an audit. I read `v4/flock-recursive` at `41438c3` (worktree has
uncommitted S-H4/RET edits) and `v4/rev44` at `e4b7d5f` (A2″ uncommitted). I ran no Lean builds.
Line numbers refer to the main worktree unless a path says `rev44`. The harness files are
`logs/org20`, which I diffed file by file against the core at `64378d2`: every tracked file is
identical.

Findings are ordered most important first. Each has evidence and an action.

---

## F1. What `Open4` still assumes once `nd` exists (Q1)

`Open4` (`lean/FRSubmission4Cert.lean:36–37`) is `∃ D : NodeDec4 ndNone, ∀ vk, Resid4H …`.
`Resid4H` (`lean/FRSoundness4XRunG.lean:76–84`) has two fields: `slots` (an `I`, an `rd`, and
`hRes : StmtN4 → NodeResid4`) and `links` (`hL`). The intended discharge of `slots` is
`I4`/`rd4 pf` with `resid4_of` (`FRNodeSound4R.lean:300`) ∘ `gap4_of_rows`
(`FRNodeRows4PackSound.lean:361`). After `nd` replaces `ndNone`, this is the full list:

| # | Hypothesis | Where | Discharged by | Status |
|---|---|---|---|---|
| 1 | `NodeDec4 nd` (`Links`, `readW`, the decode law) | `FRX4Ext.lean:633` | S-H4 (main) | running |
| 2 | `DecOk4 nd` (wf, safe, `cost ≤ decBudget4`, outs, size ≤ 2^19) | `FRX4Prog.lean:95`; today `decOk4_ndNone` in `certificate_sub4` | S-H4 | running; it is **not inside `Open4`**, so it must be added when `ndNone` is swapped |
| 3 | `PfHdr pf` (`reassemble`'s byte 0 is the seed query's byte 71) | `PackSound.lean:257` | S-H4's `reassemble`, as edited by A2″ (fields D, A) | planned |
| 4 | `Gap4R.imp` = `SlotImp` (run on the trace, aux/import/foreign facts, `stmtOk4`) | `PackSound.lean:301`; `FRNodeSound4.lean:159` | B1′ → B2′ → B3 (`gap4Imp_of_arena`, the 12/79 foreign flags), then C1 (R keys) and D1/reserve (`evalM`), through `slotImp_of_rep`/`RepOk` (`FRNodeRows4Rep.lean:306–331`) | planned; **D1's fixed point is unproved** (F3) |
| 5 | `Gap4R.kindS`, `.wf` at `i ≥ 1` (unaligned sub-slots) | `PackSound.lean:303–306` | A1′ (R-A′ spacers); PACK §7.1, A1′'s definition of done | planned |
| 6 | `Gap4R.aggChk` (`V_A`'s checks against `c_A`) | `PackSound.lean:307–311` | B4 | planned |
| 7 | `Gap4.wots`, `.aggPad`, `kindN`, `kindS@0`, `wf@0` | — | already theorems (`wots_aggPad_of_rows` `:315`, `gap4_of_rows`) | closed |
| 8 | **`hL`**: on a good log, an accepted in-domain node run has `es` with `D.Links` **and `Rel (S.acc vk) c (D.readW κ L es)`** | `FRSoundness4XRunG.lean:81–83` | "S-H4" (QUEUE residuals 5–7; `X4-RESULT.md:76`: "with S-G's link discharge, 3.x's `rel_readWit`") | **not covered by any rev44 track** |

**Flagged: row 8 (`hL`).** `Rel … (readW …)` is the node soundness statement over the decoded witness.
The 3.x analogue `rel_readWit` (`FRNodeSoundA.lean:223–238`) takes `NodeResid` as a hypothesis, so `hL`
needs everything in rows 3–6 (all of rev44's binding work), plus a lemma that `readW κ L es` decodes
the same `w` that `rd4 pf` reads. No 4.1 `rel_readWit4` exists (`grep` finds none). PACK §7's table
(`rev44 …/PACK-4.4.md:575–589`) has no row for `hL`, for `NodeDec4`, or for porting `nd` to the
rev44 format.
**Action:** S-H4 should prove `hL` now as `hL_of_res`, taking `hRes` at `I4`/`rd4 pf` as a
hypothesis: `nodeRun_X` (`FRSoundness4XLaws.lean:109`) gives `StmtN4` for the run's `w`, `hRes`
gives `NodeResid4`, and a new `rel_readWit4` relates that to `readW`. This decouples `hL` from
rev44's timeline. Then add a scheduled row "S-H4 port to rev44 (`nd`, `reassemble`, `hL_of_res`)"
between A2″ and F.

**Flagged, small: the H-form wiring.** `gap4_of_rows` feeds only the G forms, which still carry
`SegOut4` (`PackSound.lean:457–496`, `Resid4GR.out`). `Open4` uses the H form. No `Resid4H` built
from `Gap4R` exists yet. The composition is direct: `⟨I4 …, rd4 pf, I4_rows …, fun … hS =>
resid4_of … hS (gap4_of_rows pf hpf hS (hGap …))⟩`.
**Action:** restate `Open4` now as `∃ pf, PfHdr pf ∧ (∀ vk κ w c₁ c₂, StmtN4 … → Gap4R …) ∧ ∃ D,
∀ vk, links`, and delete the G forms (QUEUE already lists "drop `hO`/`out`, then delete the G
forms"). `Open4` then names exactly the open rows above, and progress becomes kernel-visible. Do F2
first, though, because this import change triggers it.

## F2. The certificate closure that will be checked is much larger than the one measured

`Solution`'s closure today is **240** of 372 modules. It does **not** contain `FRNodeRows4PackSound`,
`FRNodeSound4R`, `FRNodeSound4K` or S-E13a/b's rows (computed from the `import` lines). Importing the
`PackSound` route (F1) adds **91 modules**:

- **75 of them come in only because `FRNodeRead4.lean:4` imports the 3.x `FRNodeSoundA`.** That
  drags in `FRSoundnessExtLinks`, `FRXNodeRun`, `FRXLeaf` and the rest. These 75 cost **≈ 597
  CPU-s** by S-I's per-module times (`logs/S-I/run-40810876665/build-modules.txt`).
- `FRNodeRead4` uses only `Read.digestOf`, `readSigned` and `Read.readItems` from that closure.
  rev44's `FRNodeRead4` has the same import.
- The other 16 (S-E13a/b, S-E14) are untimed, ≈ 130 CPU-s by PACK §7.2.

The two cert probes, 696.2 s (G3, 7763) and 565.3 s (RET-3, `logs/probe-cert-ret3/…/cert.json`,
Intel 8370C, 241 modules), measure the 240-module closure. The QUEUE ruling "the certificate build
(696 s) fits with 1.7×; build-budget tracks wind down" therefore rests on a closure that is not the
one that will be certified. **`kernel_s` stayed at 600 s** (`season.toml:18`). A kernel timeout is
PROVISIONAL, never ACCEPT (`evaluate.py:292–300`, `AGENTS.md:593–594`). The kernel step is still
unmeasured on the real path (S-I F5); H-cert's proxy was ≈ 330 s on the 7763.
**Action:**
1. Re-point `FRNodeRead4` off `FRNodeSoundA` (move the three definitions down). A1′ already edits
   `FRNodeRead4`.
2. Run `probe/si-cert` and H-cert's KReplay proxy with a probe `Solution` that imports
   `FRNodeRows4PackSound`. That gives build and kernel times for the real closure on the 7763.
3. Keep RET-3/G4 alive until that number is in.

## F3. Decide D1 against the §8 reserve now, before A2″ freezes `seq4` (Q2, Q3)

- D1's Lean depends on "`replay_mle`/`replay_sound` + the fixed point (S-E6 §4's blocker, unproved
  so far)" (`rev44 …/PACK-4.4.md:694`).
- The reserve is a `seq4` change: a new phase, R4/P4 positions, an S-C sumcheck family.
- PACK §8 (`:697–707`) itself says the reserve should be appended in the same regeneration as the
  cap check if the kill line is likely to be hit.
- A2″ is regenerating `seq4` now. Choosing the reserve after D1 fails costs a second `seq4`
  regeneration, an A3′ re-run, a re-dump and a prover re-port.

For ACCEPT, proof risk matters more than §8's 0.1–0.2 s of `S`.
**Action:** run a bounded spike on the `replay_mle` fixed point now, in parallel with A2″. If it does
not close, take the reserve and fold its phase into A2″'s phases 52–55.

## F4. Build-order defects in PACK §7 as amended (Q3)

1. **B0 is held for P2⁹** (QUEUE "B0 … commits together with P2⁹'s re-embedded plan form"). B1′
   depends on B0 (`PACK:579`), and B2′ on B1′. rev44's prover is already inconsistent with its V
   until E1. **Action:** land B0 on rev44 directly; don't gate rev44's Lean on main's prover.
2. **C0 precedes B4 but templates B4's `aggChk` rows** (`PACK:581` against `:583`). **Action:**
   split C0: the WOTS/`aggPad`/link templates after B2′, and the `aggChk` templating after B4.
3. **Could start now but are not scheduled:**
   - B3's generic `compileFromX_run`/`AskBound` induction, stated against an abstract arena
     interface (it mirrors S-E14's `compileFromX_soundR`, `PACK:306–348`);
   - C1's `R` keys, which live in the spare region and do not read the arenas;
   - F1's `hL_of_res`;
   - F2's import re-point.
   All four are independent of A2″'s literals.
4. **A1′ and A2″ both edit `FRNodeKinds4`/`FRNodeLayout4` literals** (PB-m11). QUEUE's rev44 line
   has A1′ after B2′. That is fine, but A1′'s brief still quotes A2′'s stride (24,133). Under (β′)
   with L2 the stride is 24,222 (`PACK:952`). **Action:** re-issue A1′'s brief at §11.4's constants.
5. **S-H4 builds `nd` on main's format:**
   - `piSizeOf seq4 = 798,192`;
   - `FRX4Prog.szPs` literal;
   - `reassemble` without the D/A fields.

   A2″ changes all three (`PACK:575`, §11.4 items 1 and 6). **Action:** S-H4 states everything
   through `piSizeOf seq4`/`itemsOf seq4`, not literals; `DecOk4.safe` already does
   (`FRX4Prog.lean:99`). The port is the unscheduled row of F1.
6. **F's definition of done still says `evaluate.py cert ≤ 600 s`** (`PACK:589`). The caps are now
   build 1,200 s and kernel 600 s. **Action:** state both, measured on the closure of F2.

## F5. Is there a shorter path? (Q2)

No rule makes a residual unnecessary:

- The contract's `Certificate` (`logs/org20/RecursionFast/Contract/Certificate.lean`) needs
  `secure`, `complete`, `computes` and the caps.
- The comparator demands the exact rendered `certified` (`Challenge.lean.in`) with the three
  standard axioms.
- Nodes are inside `InDomE`, so `E` must decode them within fuel (B-15); `nd` cannot be dodged with
  the outside-domain search.

What the rules do allow:

- **Truncation does not block ACCEPT.** `evaluate.py:443–444`: ACCEPT needs `cert ok` and
  `benchmark pass`; truncation only sets `comparable: false`. Stream-time levers (P2⁹,
  `splitMin`, …) are off the ACCEPT path. Run them only with spare slots.
- **`main` can never ACCEPT.** Its node circuit leaves the imports unbound (`Gap4.imp` is false
  there, QUEUE "Node-circuit gaps"). Every soundness item (S-H4 included) should target rev44's
  format; main stays the PROVISIONAL benchmark vehicle.
- **N8 is the only kind that needs L1 + L2** (§11.2), and L2 is what forces PB-M2's 3.x
  ladder/position-lemma churn. L4 (7 slots) was rightly rejected: both step-1 chains
  `> 3·2^18` has probability ≈ 0.23 % under the `1/n²` draw, and a lost step ends the run.
  I found no cheaper N8 alternative within the relation (step 1 must be one proof of
  `nodeStmt leafA leafB`).

**Rule the plan would violate:** the final PR must touch only `submissions/flock-recursive/`
(`AGENTS.md:1216–1220`). `v4/flock-recursive` also carries `docs/`, `probe/`, `.github/` and
`logs` links. **Action:** cut the submission PR from a clean branch holding only the root, and drop
`Solution.lean`'s "PROVISIONAL" docstring at that point.

## F6. Harness friction for the first real evaluation (Q4)

1. **`probe/si-cert/run.sh:40` no longer raises `build_s`.** Its sed matches `^build_s = 600 `, but
   `64378d2` has `build_s = 1200    #` (`season.toml:17`). The probe then runs at 1,200 s, and a
   build over that is a REJECT with no timing. The other three patterns still match. **Fix:**
   `s/^build_s = [0-9]* /…/`.
2. **`logs/org20/.core-commit` says `6d05d00`**, but its contents equal `64378d2` (diffed). Update
   the marker, since tools that trust it will mislabel runs.
3. **The latest cert probe ran on an Intel 8370C** (`probe-cert-ret3/…/machine.txt`) with the old
   caps file. It is not comparable to the 7763's 696 s. Pin the probe to the 7763 tier or record the
   CPU-s.
4. **`eval-push.yml` matches `evaluate.yml@64378d2`'s inputs** (`entry_repo`, `entry_sha`,
   `entry_path`, `core_ref`, `season`, `split`; `nanoda` defaults to false). OK.
   `.github/workflows/evaluate-entry.yml` is **not** the `64378d2` `ci-template` with the pin
   substituted: it still has the old summary fields (`T_tree`, `t_link`) and lacks review m-6's
   sanitising. It is orchestrator infrastructure, not the entry's file. Re-copy it at the next
   workflow commit.
5. **`claim.json`:**
   - `qV` 36,000 stays valid: rev44's `qV4` is `4·8,783 + 3 = 35,135`.
   - The control `not_boundsOK_qV` (`FRSubmission4Cert.lean:61–65`) hard-codes 35,999. It becomes
     **false** when `qV4` drops, so the build breaks. State it at `qV4 − 1`.
   - The fuel numbers (`2^47.58 + 8192 t ≤ 2^48 + 2^16 t`) are unaffected.
6. **`ready`/handshake.** The prover prints `ready` after `Pre::new`, the plans and the prefault
   (`prover/stream.rs:266–284`); P2 measured 0.48 s against `ready_s` 10. rev44 adds the arenas and
   cap-check templates to the node data loaded before `ready`. Re-measure in E1.
7. **`step_s` = 60 at step 1's worst case** (two chains near `2^20`: 8 segments plus N8). The
   blueprint's segment model gives ≈ 45–52 s (BLUEPRINT B-11/B-13 rows, `:1966`). I found no
   measurement of that request as one process. rev44 adds the D/A writes. A timeout fails the run.
   Both chains are `> 2^19` with probability ≈ 2 %. **Action:** add a worst-case `prover first`
   KAT, two `2^20` chains on the 7763, to E1's definition of done.
8. **Comparator memory.** The default cap is `--cert-mem 14G` (`evaluate.py:459`); H-cert measured
   3.2 GiB per export. This is fine, but recheck it with F2's closure.
