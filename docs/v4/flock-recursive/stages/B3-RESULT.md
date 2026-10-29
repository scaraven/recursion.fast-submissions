# B3 (track L-circ): RESULT — `compileFromX_run`, the run's existence on the read trace (PACK-4.4 §4)

Base: HEAD `69d0c4e` (worktree `recursion.fast-submissions-flock`, branch `v4/flock-recursive`).
Build tree `logs/fr-build-B3` (copy of `fr-build-orch`, `MINE="FRNodeRun4 FRNodeRun4S
FRNodeRun4Ctrl"`, against `logs/org20`). Logs: `logs/B3/`. Every lake/lean command ran in the 16G
scope under `timeout`. No sub-agents. Nothing committed. **No existing module was edited.**
Journal: `B3-JOURNAL.md`.

## Status

| Item | State |
|---|---|
| Generic theorem | **Done**: `compileFromX_run` / `compileX_run`, generic in the extension `X`, the replay template `RT`, the ask template `AT`, the program and the trace. |
| Instance at the slot prototypes | **Done**: `slotImp_of_runA` (S-N2's `SlotImp`, the run included) and `gap4Imp_of_run` (`Gap4.imp`'s form), with the per-item obligations as an interface (`ATOk`/`AskBound`). |
| Controls | Done (§4), including an end-to-end run of `compileX_run` on a program with an ask. |
| `lake build FR FRNodeRun4 FRNodeRun4S FRNodeRun4Ctrl` | **green**, 2,606 jobs (`logs/B3/build-final.log`). |
| Axioms | 27 declarations ⊆ {`propext`, `Classical.choice`, `Quot.sound`}, no `sorryAx` (`logs/B3/axioms.log`, `logs/fr-build-B3/ax/AxB3.lean`). |
| Source rule | `python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`: 389 files, 0 findings (`logs/B3/source-rule.log`; the count includes another track's untracked `FRXOut4C.lean`). |
| `FR.lean` (orchestrator) | add `import FRNodeRun4Ctrl` (it pulls in the other two). |

## 1. What was built (`loc.py`, `logs/B3/loc.txt`: total / code / thm)

| Module | total / code / thm | Content |
|---|---|---|
| `FRNodeRun4` | 538 / 395 / 24 | **`execA`** (the answer-driven run), `execA_some`, `execA_of_exec`, `execA_prefix`; **`PrevOk`**, **`AT`**, **`AskCtx`**, **`ATAsk`**, **`ATImp`**, **`ATOk`**, **`AskBound`**, `atAsk_of_askBound`, `askBound_of_atAsk`; the cell readings `prev_piField`, `rep_of_invK`, `digest_of_rep`, `rd_of_cells`, `rd_of_piField`, `absorbQ_of_links`, `squeezeQ_of_links`, `nodeQ_of_mux`, `seedQ_of_pre`, `colQ_of_pre`, `ans_of_cells`; **`askRowsX`**, **`impAX`**, `impAX_sub`; **`compileFromX_run`**, **`compileX_run`** |
| `FRNodeRun4S` | 144 / 89 / 7 | `item_at`, `items_uni`, **`protoProg_items`**, **`execA_proto`**; `askRowsP`, `impAP`, **`SlotRunA`**, `AskHolds`, **`SlotImpA`**, **`slotImp_of_runA`**; `askIRows4`, `askHolds_of`, **`gap4Imp_of_run`** |
| `FRNodeRun4Ctrl` | 208 / 141 / 14 | the controls (§4) |
| **total** | 890 / 625 / 45 | |

### 1.1 The shape, and why

`exec` stops only at an ask whose computed query differs from the trace entry (or an exhausted
trace). The difficulty in stating the run theorem like S-E14's soundness is that `SlotRun`'s
auxiliary, import and foreign facts are about the run's final state, which the theorem has to
build. The **answer-driven run** `execA` (`exec` without the query comparison) settles it: it
exists as soon as the trace has an entry per ask, and its final state depends only on the trace,
so the residual facts can be stated on it. The theorem then shows that `exec` follows the same
run.

```lean
def ATAsk impl X A κ inp w tr : Prop :=
  ∀ P cs pre op k regs q e, AskCtx impl A κ inp w P cs pre op k regs →
    evalOp impl κ inp regs op = .ask q → tr[k]? = some e →
    e.1 = q ∧ List.Forall₂ (RepS w) (stepOut X P cs op).slots [.d e.2]
def ATImp impl X A κ inp w : Prop :=
  ∀ P cs pre op k regs vs ok, A.cov op = true → AskCtx impl A κ inp w P cs pre op k regs →
    evalOp impl κ inp regs op = .vals vs ok → (stepOut X P cs op).imp = true →
    List.Forall₂ (RepS w) (stepOut X P cs op).slots vs
-- AskCtx = SelOk ∧ InvK w cs regs κ ∧ PrevOk impl κ inp pre regs ∧ (A.rows P cs pre op k hold)

theorem compileX_run (hX : ExtOkK impl tc X κ) (hR : RTOk impl X rt κ) (hA : ATOk impl X A κ inp w tr)
    (base) (hP : SelOk w P κ) (he : execA impl κ inp ops St.init tr = some (s, tr'))
    (hr) (ht) (hx : aux facts at s)
    (hi : ∀ i ∈ impAX X P rt A (CS.init base) ops, RepS w ((compileX X P base ops).slot i) (rd s.regs i))
    (hrr : ∀ r ∈ repRowsX X P rt (CS.init base) ops, r.Holds w)
    (hra : ∀ r ∈ askRowsX X P A (CS.init base) none 0 ops, r.Holds w) (hf : foreign flags at s) :
    exec impl κ inp ops St.init tr = some (s, tr') ∧ s.ok = true ∧
      ∀ i, RepS w ((compileX X P base ops).slot i) (rd s.regs i)
```

- **Along the trail, never over the ops.** `askRowsX`/`impAX` are folds identical to `compileFromX`.
  `ATOk`, like S-E14's `RTOk`, is quantified over every compile state, so it is proved once per
  template and never evaluates a program. The induction is S-E14's `compileFromX_soundR` almost line
  for line. The vals branch gains a third import source (`A.cov`). The ask branch takes the answer
  register's representation from `ATAsk` instead of the import hypothesis, and passes `exec`'s check
  with `e.1 = q`.
- **The previous op (`pre`, `PrevOk`).** An ask's byte operand (`askSeed`'s `hdr`, an absorb's
  message, a column) is a `Val.b`. These are untracked (slot `none`), so `InvK` says nothing about
  them. In every generator (`seedOps4`, `absorbOps`, `uniOps`, `posOps4`) the byte operand is the
  register appended by the `piField` immediately before the ask. The obligation therefore sees `pre`
  and the fact that `pre`'s results are the last registers. `rd_of_piField` turns that into
  `rd regs m = .b (π.extract …)` once the template checks `m + 1 = cs.slots.size`.
- **`ATImp` / `AT.cov` (a deviation from the memo's sketch).** S-E14's `RTOk` is quantified over
  every input, so no replay template can bind a proof field: a `piElem`'s value is `inp.π`'s bytes.
  `ATImp` is the same obligation at the fixed input and trace. It is the binding PACK-4.4 §1.3 calls
  "alias to the arena cells of the payload", and the same holds for `chF`/`chK`, `bitOf` and `input`.
  Without it, every such class would remain a residual import, stated on concrete registers of the
  106 k-op run.
- **The answers are not assumed.** `impAX` excludes asks: each answer register's representation
  comes from `ATAsk`. It holds by aliasing to arena₁ or, with today's compile (fresh import cells
  on `cs.next`), by two rows per ask tying those cells to the arena.

### 1.2 The instance (`FRNodeRun4S`)

- **`protoProg_items`**: both prototypes ask `itemsOf seq4`. The proof goes through the group
  programs' `Forall₂ UniRel` to the kind programs, then `Op.at` keeps `item?`, then `items_gen4`. With
  `itemsOf_seq4_len`, the answer-driven run on any 8,905-entry trace exists and uses it up
  (`execA_proto`). Hence `slotTr4_length` discharges the length.
- **`SlotImpA rt A impl₀ base κ v w inp tr`**: at each index `ι` the selectors may pick, three facts:
  - the ask obligation `ATOk (implP … ι) (Xof π) (A π) ι inp (slotAsg κ v w) tr`;
  - **`SlotRunA`**: the aux facts, the residual imports `impAP rt A π` and the foreign flags, on the
    answer-driven run;
  - `stmtOk4`.
- **`slotImp_of_runA`**: from `SlotRows`, `RepHolds rt` (S-E14), `AskHolds A` and `SlotImpA`, derive
  `SlotImp`. `SlotImpR` follows by S-E14's `slotImpR_of_imp`.
- **`gap4Imp_of_run`**: `Gap4.imp`'s form from four inputs:
  - `StmtN4`;
  - the folds `repIRows4 rt κ v ⊆ nodeIRows4 κ` and `askIRows4 A κ v b ⊆ nodeIRows4 κ` (rows at
    `v·2^20 + b + k`, `b` a parameter);
  - `SlotImpA` at every active slot.

## 2. The interface for B4 and B2′ (what is missing, exactly)

To turn `Gap4.imp` into a theorem on rev44, the row side supplies the following.

1. **An ask template `A π` per prototype** with `ATOk` at every slot and selectable `ι`, on the
   reader's input and trace (`slotIn`, `slotTr4`).
   - Since `ATOk` holds for all `cs`, the template checks its pattern on `cs`: the slot shapes
     `some (.d, [l₀, l₁])`, `m + 1 = cs.slots.size`, and `pre = some (.piField …)`. Elsewhere it emits a
     failing row such as `0·0 = one`, as `pinSq` does.
   - Completeness, meaning the honest rows hold on the real programs, then needs the pattern to hold
     at every ask. It does by the generators. This is checked on the dump, not by the kernel.
   - Per field of `AskBound`, the per-item facts:

     | Field | The per-item fact (helper) | From |
     |---|---|---|
     | `absorb`/`squeeze` | the state slot's two cells carry `x` and entry `k` is `absorbQ x (π's field bytes)` / `squeezeQ x` (`absorbQ_of_links`, `squeezeQ_of_links`, `rd_of_piField`) | the FS link (state cells = item `k`'s state cells, or the previous answer's), the H bridge, the pins, `reassemble`'s positional spec (B3 of S-E13a) |
     | `node` | the `l`, `r` slots carry `x`, `y` and entry `k` is `nodeQF i x y` (or `0^64` halves where `act` fails) (`nodeQ_of_mux`) | the Merkle mux rows (`selectHalf`'s rows as compiled), the sibling alias `l + r + a·cur`, the H bridge, the pins |
     | `seed`/`col` | entry `k` is `seedQ vk c (π[0,48))` / `colQ i (π's column bytes)` (`seedQ_of_pre`, `colQ_of_pre`) | the pins, `reassemble`, `PubCells4` for `vk`/`c` |
     | `ans` | the answer slot's cells carry entry `k`'s answer (`ans_of_cells`) | arena₁ alias, or 2 rows per ask on today's import cells |
     | `ATImp` (`A.cov`) | a covered op's import slots represent its value at `slotIn` | the §1.3 aliases (proof fields → arena payload cells, `chF`/`chK` → answer halves, `bitOf` → L bits, `input` → seed/`hashA` cells) |

2. **The fold**: `askIRows4 A κ v b ⊆ nodeIRows4 κ` (S-E13a's `FRNodeRows4` owns it), with `hfit4`'s
   row bound for the chosen `b`.
3. **`SlotRunA`** for what `A` does not cover: the aux facts (`felems` → arena₂, `bits 20` → L), the
   residual imports `impAP`, and the foreign flags. Each is stated on the answer-driven run, a
   function of the trace.

No lemma in another track's module is needed for B3 itself.

## 3. Deviations from PACK-4.4 §4

- §4.2 sketched `hs : StreamOf w b0 tr` and `AskBound` as rows. Here the H bridge is inside the
  obligation (`ATOk` is stated for the fixed `w` and `tr`), so the generic theorem is independent of
  the arena layout, which is still moving on rev44. The rows are a template (`AT`), as in S-E14.
- The sketch's invariant `tr_rest = drop (asksSoFar cs) tr` is the induction's `tr.drop k`, with
  `k` threaded through `askRowsX` rather than read off `cs`.
- **Added `pre`/`PrevOk`** for the byte operands (§1.1).
- **Added `AT.cov`/`ATImp`**, for proof fields and other aliases at the fixed input (§1.1).
- The conclusion is `SlotImp` itself, not only `SlotImpR`. The final invariant represents every
  register, the ask imports included.

## 4. Controls (`FRNodeRun4Ctrl`, and the converses in `FRNodeRun4`)

| Definition | (+) | (−) |
|---|---|---|
| `execA` | `execA_of_exec` (a run is an answer-driven run: `SlotRunA` assumes nothing on another state) | `execA_ne_exec`: on an entry with the wrong query `execA` runs and `exec` is `none` |
| `ATAsk`/`ATOk` | `atOk_nil` (no entries); `pinSq_ok`: a real template (one squeeze of the preceding `input 0`, answer cells pinned) is sound for `[(squeezeQ vk, a)]` | `atOk_none_neg`: without rows, an entry the program does not ask breaks it; `pinSq_neg`: the same template on a wrong trace |
| `ATImp` | `atOk_nil` (covers nothing) | `atImp_neg`: covering `input` without rows fails (`vk = 1^32`, cells `0`) |
| `AskBound` | `atAsk_of_askBound` | `askBound_of_atAsk`: it asks nothing beyond `ATAsk` |
| `impAX` | `impAX_sub`: ⊆ `impRX` (so ⊆ the compile's imports) | `run_ctl`: `impAX` of `[input 0, askSqueeze 0]` is `[0]` (the ask is excluded) |
| `compileX_run` | **`run_ctl`**: on `[input 0, askSqueeze 0]` with `pinSq`, every hypothesis is met at a concrete assignment and `exec … = some (⟨#[.d 0, .d 0], true⟩, [])` | — |
| `protoProg_items` | used by `execA_proto` | — |

The control programs have two ops. The `rfl` steps evaluate only those programs.

## 5. Measurements

Sequential profile: one core (`taskset -c 31`), `-DElab.async=false`, 16G scope, load ≈ 6.5.
Logs are `logs/B3/profile-*.log`.

| Module | Type checking | Tactics | Max RSS | Wall (mostly import) |
|---|---|---|---|---|
| `FRNodeRun4` | 0.29 s | 1.75 s | 2.88 GB | 11.4 s |
| `FRNodeRun4S` | 0.12 s | 0.19 s | 2.83 GB | 7.2 s |
| `FRNodeRun4Ctrl` | 0.19 s | 0.52 s | 2.83 GB | 8.7 s |

Nothing in the certificate changes until B4 folds `askIRows4` and uses `gap4Imp_of_run`. The
certificate's cost is then only these modules' check, about 0.6 s of kernel time.

## 6. Open questions

1. **Merge.** These modules import only HEAD modules (`FRNodeRows4Rep`, `FRSoundness4Qry`). On
   rev44, `protoProg_items` needs the group programs' relation there:
   - (β′)'s new FS phases change `seq4` and `itemsOf seq4`, but `items_gen4` is generic;
   - the length literal `8905` in `execA_proto`/`slotImp_of_runA` (via `itemsOf_seq4_len` and
     `slotTr4_length`) moves with them;
   - the generic part does not depend on `seq4`.
2. **Rows per answer.** Today's compile puts each ask's answer on fresh import cells. Two options:
   - B4 ties them to the arena by 2 rows per ask (≈ 17.8 k rows per slot);
   - B2′'s compile aliases them (0 rows). Both meet `ATAsk.ans`.
3. **The cap read under (β′).** This is `piDigestAt`, an import whose value depends on a register
   (`k = j >> sib`). It fits `ATImp` (operands through `InvK`, `π` fixed), but its binding is
   (β′)'s batched check. It is the one `A.cov` class whose template is not an alias.
