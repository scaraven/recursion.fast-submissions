# S-H2 RESULT: the extractor program (track L-ext, second half), first part

Base `53c2e13`. **Delivered:** `ext`, `E`, `fuel`, and `computes : Computes ext E fuel`. This is
the certificate's `computes` conjunct, kernel-checked with the three standard axioms. The cap
facts `fuel ≤ B` and `size ≤ progCap` are also proved. The `W` and `bad` cases of `ext_good_tape`
are proved. The SNARK branch is a parameter. Every theorem is proved once for any SNARK branch
`dec` with `DecOk dec`. The shipped `ext` uses the empty branch `decSnark` for now.

**Not delivered:** the decoder (BLUEPRINT §6.2 steps 2–5: `FRXLog`, `FRXDecodeA/B`) and the SNARK
case of `ext_good_tape`. On a SNARK proof, the current `E` is `none`. The `computes` conjunct is
nevertheless true and final: it holds for every `dec` with `DecOk`, so plugging in the decoder
re-proves nothing above it.

## 1. Files (code lines by the core's `scripts/loc.py`)

| Module | total | code | theorems | content |
|---|---|---|---|---|
| `FRXProg` | 208 | 112 | 8 | `Safe`, `boundsOk_of_safe`; the parse, the `W` branch `wIR`, `extIRWith dec`; `memX = 2^26`, `mpwX = 3`; `fuel`, `decBudget`, `DecOk`; `wf_extIRWith`, `cost_extIRWith`, `sizeIR_extIRWith`, `fuel_covers`, `fuel_le_budget`, `size_extWith` |
| `FRXComputes` | 304 | 220 | 27 | `Eof` (B-8), `computes_Eof`; `toNat_ceil8`; tape lemmas; `parse_regs`, `wPre_regs`, `wLoop`, `wIR_sem`; `safe_wIR`; `halts_of_tape`, `halts_with`, **`computesWith`**; `decSnark`, **`ext`, `E`, `computes`, `ext_caps`** |
| `FRXSpec` | 277 | 197 | 18 | `kindFlag`, `parse_isK`, `kindFlag_byte`, `tape_byte0`; `run_W_tape`, **`run_W`, `E_W`**, `run_bad_tape`, **`E_bad`**, `ext_W`, `ext_bad`; controls |
| **total** | 789 | 529 | 53 | |

The load-bearing statements, all in `FR.X`:

```lean
def ext : XProg := extWith decSnark                    -- toProg 2^26 3 (extIRWith decSnark)
def E : Digest → Proof → Log → Option Wit := Eof ext fuel
def fuel (t : ℕ) : ℕ := fuelBase + fuelPerWord * t      -- 2^46 + 2^12 t (claim.json)
theorem computes : Computes ext E fuel
theorem ext_caps : (∀ t, fuel t ≤ extractorBudget t) ∧ ext.body.size ≤ progCap
theorem computesWith {dec} (hd : DecOk dec) : Computes (extWith dec) (Eof (extWith dec) fuel) fuel
theorem E_W {dec} (hd : DecOk dec) (c π L) (hW : kindOf π = .W) (hπ : π.size < 2 ^ 64) :
    Eof (extWith dec) fuel c π L = WitnessSending.decode π
theorem E_bad {dec} (hd : DecOk dec) (c π L) (hb : kindOf π = .bad) (hπ : π.size < 2 ^ 64) :
    (extWith dec).run (extractorInput c π L) (fuel _) = some [] ∧ Eof (extWith dec) fuel c π L = none
```

`DecOk dec` asks five things of the SNARK branch:

- it is well formed (`WF`);
- it is `Safe` on every domain tape with `|π| = piSize`;
- `cost dec t ≤ decBudget t = 2^46 − 2^27 + (2^12 − 16)·t`;
- `outs dec t ≤ outCap`;
- `sizeIR dec ≤ 2^19`.

## 2. How `computes` is proved

The program is `parse ; if isKind then (if |π| = piSize then dec else skip) else wIR`.

- **The parse.** It reads tape word 4 (`|π|`) and the low byte of word 5, exactly as `kindOf`
  does (S-0-m5).
- **The `W` branch.** It sets `⌈|π|/8⌉` as `(w >> 3) + (0 < w & 7)`, never `+ 7` (the S-H1
  note). It then copies that many tape words from word 5 in a `loopT` with cap `t` (BP-C-R2-M2).
- **The loop bounds.** `Safe` is syntactic and gives `BoundsOk` from every `Inv` state.
  - The `W` loop's count is bounded on the tape (`safe_wIR`).
  - The SNARK branch is entered only when the flag says `|π| = piSize`. `hpi` turns the flag into
    `π.size = piSize`, and from that `DecOk.safe` gives the branch's bounds.
- **Halting and the output length.** `run_toProg` gives halting within the fuel (`fuel_covers`).
  The output length is bounded per branch:
  - `W`: exactly `⌈|π|/8⌉ ≤ 2^17` words (`wIR_sem`);
  - `bad`: `0` words;
  - SNARK: at most `outs dec ≤ outCap` (`outs_le`).
- **The `E` conjunct.** `E := Eof ext fuel` makes it hold by definition (`computes_Eof`, B-8).

## 3. Build and kernel times (logs in `logs/S-H2/`)

- **Build.** `lake build FRXProg FRXComputes FRXSpec`, with the dependencies already built, takes
  18.8 s wall (`build.log`).
- **Sequential elaboration** (`lean -DElab.async=false --profile`, one module at a time;
  `*.profile`, `profile-summary.txt`):

| Module | wall | import | type checking | simp | tactics | max RSS |
|---|---|---|---|---|---|---|
| `FRXProg` | 9.8 s | 3.8 s | 0.33 s | 0.48 s | 1.5 s | 2.6 GB |
| `FRXComputes` | 10.8 s | 3.7 s | 0.60 s | 1.65 s | 1.2 s | 2.6 GB |
| `FRXSpec` | 14.2 s | 3.5 s | 2.33 s | 2.9 s | 1.8 s | 2.7 GB |

Kernel ("type checking") in total: about 3.3 s. Nothing evaluates the `2^26`-word memory or a
large program. The kernel runs use a 260-word toy memory.

## 4. Controls

| Control | Kind | Shows |
|---|---|---|
| `ext_encode` | positive, every size | `E c (encode w) L = some w` for every `w` that fits the format: the real `ext` recovers every witness-sending witness |
| `E_W`/`ext_W` | positive | on a `W` proof, `E = WitnessSending.decode π`, including proofs above `proofCap` |
| `E_bad`/`ext_bad` | negative (ill-formed tape) | a kind byte with `|π| ≠ piSize` halts within the fuel with no output, so `E = none` |
| `toy_W` | kernel run | the compiled code with a 260-word memory, on `[0,0,0,0, 9, 0x1100, 0x22, 0]`, outputs `[0x1100, 0x22]` |
| `toy_W_exact` | kernel run, fuel tightness | 340 fuel suffices and 339 does not (260 words of memory and 80 steps) |
| `toy_bad` | kernel run, negative | first byte `'N'` with `|π| = 9` outputs `[]` |
| `decOk_decSnark` | interface | the empty SNARK branch meets `DecOk` |

`FRXDsl`'s `toyBad_short`/`toyBad_not_bounds` remain the negative control for an under-declared
`loopT` cap.

The "toy tape decoded correctly" control for the RS decoder belongs to the decoder stage. It was
not delivered.

## 5. Checks

- **Axioms.** `computes`, `computesWith`, `ext_caps`, `E_W`, `ext_bad` and `ext_encode` depend on
  `propext, Classical.choice, Quot.sound`. The toy runs depend on `propext, Quot.sound`.
- **Source rule.** `python3 -I .contract/scripts/source-rule.py submissions/flock-recursive`:
  53 files, 0 findings.
- **Hygiene.** No `sorry`. The only remaining warnings are `if_pos`/`if_neg` deprecations, which
  other modules also have.

## 6. Deviations from the blueprint

1. **The fuel is `claim.json`'s `2^46 + 2^12 t`, not §6.3's `2^47.5 + 2^12 t`.**
   - With `2^46`, the SNARK branch may cost at most `decBudget ≈ 2^46 − 2^27 + 2^12 t`.
   - §6.3's estimate for the decoder is `2^46.52 + 2^11 t`, so it would **not fit**.
   - `fuel` is defined from the two constants `fuelBase`/`fuelPerWord`. Raising `fuelBase` (for
     example to `3·2^46 = 211,106,232,532,992 ≈ 2^47.58`, still under `2^48`) changes one line.
     `fuel_le_budget` re-proves by `omega`.
2. **The modules are re-cut.**
   - `FRXProg` holds the frame and the parse, with the SNARK branch as a parameter (`DecOk`).
   - `FRXComputes` holds `computes`.
   - `FRXSpec` holds only the `W` and `bad` cases.
   - `FRXLog` and `FRXDecodeA/B` are not written.
3. **`Safe`** is new. It is a syntactic sufficient condition for `BoundsOk` that generalises the
   S-H1 review note. The SNARK branch discharges its `loopT` bounds through `DecOk.safe` and is
   given `|π| = piSize`. With that size, the log's length field sits at the fixed word
   `5 + piSize/8 = 94,465`.
4. **`E_W` holds for every `π.size < 2^64`**, not only up to `proofCap`. Above `2^64` bytes the
   length word wraps and the tape is ambiguous (the contract's domain note), so that case is not
   covered.

## 7. Open questions and what remains

- **Q1 (fuel).** Should `claim.json`'s `fuel_base` be raised to the blueprint's figure before
  the decoder lands? With `2^46`, the decoder as estimated does not fit.
- **Q2 (`final`'s `W` case).** `E_W` needs `π.size < 2^64`. Does `final` state that hypothesis,
  or does it get it from `μ`/`Bad`? Above `2^64` bytes the `W` verifier's decode reads a wrapped
  length word.
- **What remains for the next stage (S-H3, L-ext).** The SNARK branch `dec`:
  - the log walk and index (`loopT` over `|L|` read from word 94,465, cap `t`; then a stable
    merge sort, as `loopK 64` passes over `loopT` merges);
  - the ladder read by first-preimage lookup;
  - the per-level agreement set;
  - the butterfly inverse NTT, proved equal to `coeffsAt` via `decode_row_D`;
  - the output in `decodeWit`'s format (`witWords` of the node or leaf).

  Each phase needs a `Safe` proof, a cost lemma and a semantic lemma. The `DecOk` obligations are
  then discharged by composition, and `computes`, `E_W` and `E_bad` carry over unchanged.
- **A pitfall for that stage (journal item 5).** Tactics that decide `rd (semXIR I <concrete
  program> s).M r = 0` (`by_cases`, `rcases`, `refine ⟨_, ?_⟩` on `BoundsOk`) make the unifier
  run the concrete program and time out. Generalise the state first, and use the `Iff.rfl`
  unfolding lemmas (`boundsOk_seq`, `boundsOk_ite`, `semXIR_seq`, `semXIR_ite`).

---

## Part 2 (after the coordinator's answers): fuel `3·2^46 + 2^12 t`; log walk and sort

**Delivered.**

- **Fuel.** `fuelBase := 3 * 2 ^ 46`, matching `claim.json` (B-10). `decBudget` is now
  `3·2^46 − 2^27 + 4080 t`. `fuel_le_budget`, `ext_caps` and `computes` re-prove unchanged.
- **The log index program** (`FRXLog`). `logIR := walkIR ; sortIR`. It is the SNARK branch now:
  `decSnark := logIR`, so the shipped `ext` runs it on every proof of kind `'L'`, `'P'` or `'N'`
  with `|π| = piSize`.
  - **The walk.** It records the tape position of entry `k` in `X[k]` (cell `memX + k`). Its
    count `|L|` is read from tape word `posL = 94,465` just before the loop, and the loop is
    charged at `t / 5`.
  - **The sort.** A bottom-up merge sort of `X` (64 passes; `X → Y = X + n` and back). The key is
    (answer words 0…3, tape position), compared lexicographically and unsigned. Ties break by
    position, so the earliest entry with a given answer comes first: the first-preimage order.
    Each pass reloads its count from `posL`.
  - **Obligations.** `decOk_logIR` proves `DecOk logIR`:
    - `wf_logIR`;
    - `safe_logIR`, from `tape_count_le`: `|L| ≤ t / 5` on every domain tape of a proof of
      `piSize` bytes;
    - `cost_logIR : cost logIR t = 2592 + ⌊t/5⌋ · 11871`;
    - `outs_logIR = 0`;
    - `sizeIR ≤ 2^19`.
- **The walk's semantics** (`FRXLogSpec`, `index_spec` first half).
  - `walk_spec` proves that `X[k]` holds the tape position of log entry `k`, for every
    `k < |L|`:

    ```lean
    theorem walk_spec (c π L) (hs : π.size = piSize) (hq : ∀ e ∈ L, e.1.size < 2 ^ 64)
        (ht : (extractorInput c π L).length ≤ 2 ^ 64) (s : St) (hM : Inv s.M)
        (hsz : memX + L.length ≤ s.M.size) {k} (hk : k < L.length) :
        rd (semXIR (extractorInput c π L).toArray walkIR s).M (memX + k) =
          toWord (posL + 1 + entryOff L k)
    ```

  - `tape_entry` states that the tape word at that position is `|q_k|`.
  - `walkLoop` is the loop invariant, including the frame of the other heap cells.
  - `rd_storeM` is the guarded heap store.
- **`FRXDsl` change (same track).** `Aff` gained a divisor `d`: `eval = a + ⌊b·t/d⌋`. A count of
  log entries (at most `t / 5`) is then charged at `t / 5`. With cap `t` the sort alone would
  cost about `11,871 t`, which is over the fuel. The S-H1 controls were updated to `⟨0,1,1⟩` and
  `⟨1,0,1⟩`; all S-H1 proofs re-check.
- **Module split.** `ext`, `E`, `computes` and `ext_caps` moved from `FRXComputes` to a new
  module `FRXExt` (after `FRXLog`). `FRXSpec` imports `FRXExt`.

**Budget under the new fuel.**

| Part | Constant | Per tape word |
|---|---|---|
| memory | `2^26` | 3 |
| parse and `W` branch | 34 | 8 (`W` only) |
| `logIR` (walk ≈ 6.2 t, sort ≈ 2,368 t) | 2,592 | ≈ 2,374 |
| `decBudget` (what `dec` may use) | `3·2^46 − 2^27` | 4,080 |
| **left for phases 2–5** | **≈ `2^47.58`** | **≈ 1,705** |

§6.3's decoder estimate of `2^46.52` for the constant term fits about 2.1× under what is left.
Phases 2–5 have no linear term of their own: their lookups are binary searches, which go into
the constant term.

**Files.**

| Module | total | code | theorems |
|---|---|---|---|
| `FRXProg` | 208 | 112 | 8 |
| `FRXComputes` | 276 | 206 | 24 |
| `FRXLog` | 271 | 178 | 12 |
| `FRXLogSpec` | 260 | 215 | 14 |
| `FRXExt` | 36 | 11 | 3 |
| `FRXSpec` | 277 | 197 | 18 |
| **total** | 1,328 | 919 | 79 |

**Times.**

- **Build.** Building all `FRX*` modules after the `FRXDsl` change takes 32.5 s (`logs/S-H2/build2.log`).
- **Sequential profile** (`logs/S-H2/*.profile`):

| Module | wall | type checking | simp |
|---|---|---|---|
| `FRXLog` | 15.8 s | 0.51 s | 3.7 s |
| `FRXLogSpec` | 10.5 s | 0.82 s | 1.0 s |
| `FRXExt` | 6.1 s | 0 s | — |
| `FRXSpec` | 13.2 s | 2.45 s | 2.5 s |

**Checks.**

- **Axioms.** `computes`, `walk_spec`, `decOk_logIR` and `ext_encode` depend on
  `propext, Classical.choice, Quot.sound`.
- **Source rule.** 56 files, 0 findings.
- **Hygiene.** No `sorry`.

**Not done yet** (in order):

1. **The sort's semantics.** `X` after `sortIR` is the permutation of the walk's positions sorted
   by key. Plan: a pure Lean merge-sort model over `List ℕ`, proved sorted and a permutation; a
   pass-level lemma that one `passIR` maps the memory image of the model's list to the next one
   (the `stepIR` invariant, with blocks of width `w`); then 64 passes. This is the largest
   remaining proof in phase 1. The program may change while it is proved: any fix must keep
   `cost_logIR` within the budget above.
2. **Lookup.** A binary search over `X` (a `loopK` of 64), and its first-preimage spec against
   `FRMerkle`/`FRLog`'s first-preimage reading.
3. **The ladder read, the agreement set, the butterfly inverse NTT with `decode_row_D`/`coeffsAt`,
   and the output in `decodeWit`'s format.**
4. **The SNARK case of `ext_good_tape`**, with hypotheses for what S-G2's `final` will supply.

The pitfall noted in Part 1 held again here: every semantic proof generalises the state or the
memory before case analysis on `semXIR` (`walkBody_sem`, `walk_spec`).

---

## Part 3: the sort's key comparison (first brick of `sortIR`'s correctness)

**Delivered: `FRXSortSpec`** (180 lines, 142 code, 8 theorems).

- **Definitions.**
  - `aposW I x`: the answer position, as the program computes it.
  - `keyW I x = [a₀, a₁, a₂, a₃, x]`: the sort key, the four answer words then the position.
  - `lexW`: lexicographic `<` on word lists, unsigned.
  - `keyLt I x y := lexW (keyW I x) (keyW I y)`.
  - `bW`: a Boolean as a 0/1 word.
- **`cmpIR_sem`.**

  ```lean
  theorem cmpIR_sem (I s) (hM : Inv s.M)
      (hi : regs ≤ (rd s.M rSrc + rd s.M rI).toNat) (hj : regs ≤ (rd s.M rSrc + rd s.M rJ).toNat) :
      rd (semXIR I cmpIR s).M rF = bW (keyLt I (rd s.M (rd s.M rSrc + rd s.M rI).toNat)
        (rd s.M (rd s.M rSrc + rd s.M rJ).toNat))
  ```

  The two `regs ≤ …` hypotheses are needed. Without them the load's address could be the
  address register itself.
- **Supporting lemmas.**
  - `fold_bW`: one step of the machine's lexicographic fold equals one step of `lexW`.
  - `cmpWord_sem`, `aposIR_sem`.
  - The frames `cmpWord_frame`, `aposIR_frame`, via `FRXDsl.frame`.
- **Checks.**
  - Axioms: `propext, Quot.sound`.
  - Sequential profile: 9.8 s wall, type checking 0.26 s (`logs/S-H2/FRXSortSpec.profile`).
  - Source rule: 57 files, 0 findings. No `sorry`.

**The plan for the rest of the sort's correctness.** It is designed so that no permutation has
to be tracked.

1. **`keyLt` is a strict total order on distinct positions.** This follows from `lexW` and the
   position as the last key word.
2. **`stepIR_sem`.** Simulate one step against a pure step function on `(i, iE, j, jE, k)` and the
   memory images of `src` and `dst`. It reuses `cmpIR_sem`, the `blockIR` arithmetic (the `minPs`
   identity) and `rd_storeM`.
3. **The per-block invariant.** Within the current block `[lo, hi)`:
   - `dst[lo..k)` is strictly sorted;
   - its values lie in `src[lo..i) ∪ src[iE₀..j)`;
   - `k − lo = (i − lo) + (j − iE₀)`;
   - the last value written is below the heads `src[i]` and `src[j]`.
4. **The per-pass lemma.** If `src` is injective on `[0, n)` and its runs of width `w` are
   strictly sorted, then `dst` has strictly sorted runs of width `2w`, each `dst` block's values
   lie in the same `src` block, and `dst` is injective.
5. **After the 64 passes.** `X[0..n)` is strictly sorted (width `min(2^k, n)` reaches `n` by pass
   61) and its values lie among the walk's positions. Being strictly sorted, it has `n` distinct
   values in a set of `n` positions, so by `Finset.eq_of_subset_of_card_le` it is exactly that set.
   That is the property the lookup needs: every entry is present, sorted by key.

**Then** the lookup (a 64-step binary search for the lower bound of `(a, ·)`), and phases 2–6, as
in Part 2.

**Stopped here** on the token budget. The state is commit-ready:

- every `FRX*` module builds;
- no `sorry`;
- the source rule is clean;
- `computes` is unchanged (`ext` still runs walk and sort; their costs are as in Part 2).

---

## Part 4: the merge sort's correctness, pure form (plan steps 1, 3, 4 and 5)

**Delivered: `FRXMerge`** (436 lines, 364 code, 14 theorems).

- **Step 1, the order.** `keyLt_order : SOrd (keyLt I)`. `keyLt` is irreflexive, transitive,
  and total on distinct positions, through `lexW_irrefl`, `lexW_trans` and `lexW_total` (the
  key's last word is the position).
- **The pure machine.**
  - `MS` holds the heads `i`/`j`, the run ends `iE`/`jE`, the output index `k`, the destination as
    a function, and a ghost block start `lo`.
  - `bstart` and `mstep` mirror `blockIR` and `stepIR` operation for operation, including
    `jE = min(k + w + w, n)` and the choice rule `takeL`.
  - `mrun` is `m` steps, and `passF` is a pass (`n` steps from the empty state).
- **Steps 3 and 4.** `Good` is the per-block invariant: order of the indices, run ends,
  alignment, `k + iE = i + j`, the current block strictly sorted and drawn from its own block,
  below both heads, and finished blocks sorted and drawn from their own blocks.
  - `good_bstart` and `good_mstep` show it is preserved; `good_mrun` iterates them.
  - **`pass_ok`**: a pass on a source whose width-`w` runs are strictly sorted and which is
    injective on `[0, n)` gives `PassOut`. Its width-`2w` blocks are strictly sorted and draw
    their values from the same source block.
  - `PassOut.inj` shows the output is injective. `PassOut.runs` shows the runs of the next
    width `min(2w, n)` are sorted.
- **Step 5.**

  ```lean
  theorem passes_ok (ho : SOrd lt) (hn : n < 2 ^ 63) (X ds : ℕ → ℕ → Word)
      (hX : ∀ p, ∀ a < n, X (p + 1) a = passF lt (X p) n (wseq n p) (ds p) a)
      (hinj : ∀ a b, a < n → b < n → X 0 a = X 0 b → a = b) :
      (∀ a b, a < b → b < n → lt (X 64 a) (X 64 b) = true) ∧
      (∀ a < n, ∃ c < n, X 64 a = X 0 c) ∧ (∀ c < n, ∃ a < n, X 64 a = X 0 c)
  ```

  After 64 passes at the widths `wseq n p = min(2^p, n)` (`wseq_eq`), the array is strictly
  sorted and holds exactly the initial values. Completeness comes from a cardinality argument
  (`Finset.eq_of_subset_of_card_le`); no permutation is tracked anywhere.
- **Checks.**
  - Axioms: `propext, Classical.choice, Quot.sound`.
  - Sequential profile: 12.3 s wall, type checking 1.66 s (`logs/S-H2/FRXMerge.profile`).
  - Source rule: 60 files, 0 findings. No `sorry`.

**What remains for the sort's correctness: step 2, the machine simulation.** It is mechanical,
but it is the largest register-level proof so far.

- **`stepIR_sem`.** On a state whose registers hold an `MS` state (as words) and whose heap holds
  `src` at `S + ·` and `dst` at `D + ·`, one `stepIR` gives `mstep`'s state. It uses
  `cmpIR_sem`, the `minPs` identity `min` on words below `2^63`, the `eq`/`ltu` flags as `Nat`
  comparisons, `rd_storeM` for the `dst` write, and the heap frame for `src`.
- **`passIR_sem`.** `passIR = passF` on `[0, n)`, by induction over `iterL`. After a pass the
  bases swap and `w := min(2w, n)` (`swapPs`).
- **`sortIR_sem`.** Then `passes_ok` applies with `X 0` the walk's positions. These are
  injective because `entryOff` is strictly increasing, and `walk_spec` gives them.

**Then** comes the lookup by binary search: the lower bound of `(a, ·)` in `X`, specified as the
first entry of `L` whose answer is `a`, against FRMerkle/FRLog's first-preimage reading.

**Stopped here** on the token budget. The state is commit-ready: every `FRX*` module builds, no
`sorry`, the source rule is clean, and `ext`, `computes` and the costs are unchanged.

---

## Part 5: simulation building blocks; handover for step 2

**Delivered: `FRXSortSim`** (50 lines, 31 code, 4 theorems).

- `minW`/`minW_toWord`: `minPs`'s branch-free `min` equals `toWord (min a b)` for `a, b < 2^64`.
- `eqW_toWord`, `ltW_toWord`: the `eq` and `ltu` flags on `toWord`s are `bW` of the `Nat`
  comparisons.
- Axioms: the three standard ones (two lemmas need only `propext, Quot.sound`).
- Source rule: 61 files, 0 findings. No `sorry`.

**Handover: what step 2 needs.** This agent's context is long, and the remaining
register-level proof is best done by a fresh agent from this record.

1. **`Rel s σ`** (the registers and heap hold `σ : MS`).
   - Registers: `rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst` hold `toWord` of `i, iE, j, jE, k,
     w, n, S, D`.
   - Heap: `rd M (S + a) = src a` and `rd M (D + a) = σ.dst a` for `a < n`.
   - Bounds: `regs ≤ S, D`; the ranges `[S, S + n)` and `[D, D + n)` are disjoint and inside
     the memory; `n < 2^61`.
2. **`blockIR_sem`**: `Rel` goes to `Rel (bstart n w σ)` (the ghost `lo` is free).
   - Use `eqW_toWord` for the two `eq` flags. `XOp.and.eval` of two `bW` flags is `bW (p && q)`.
   - For the new block: `rI := k`, `rV := k + w`, `minPs rIE rV rN` (`minW_toWord`),
     `rJ := iE`, `rV := rV + w`, `minPs rJE rV rN`.
3. **The choice.** Use `ltW_toWord` for `rG`/`rH`, then the nested `ite` with `cmpIR_sem`. Its
   address hypotheses are `regs ≤ S + i` and `regs ≤ S + j`. The result is
   `rF = bW (takeL (keyLt I) src σ')`.
4. **The write.** `ite rF (rAd := S + i; i++) (rAd := S + j; j++)`, `load rV rAd` (a heap read of
   `src`), `rAd := D + k`, `k++`, and `store rAd rV`. The store goes through `rd_storeM` and
   updates exactly `D + k`; `src` is untouched because the ranges are disjoint.
5. **`stepIR_sem`**: `Rel s σ → σ.k < n → Rel (semXIR I stepIR s) (mstep (keyLt I) src n w σ)`.
6. **`passIR_sem`**. `passPre` resets `i…k` to `0` and reads the count `n` from `posL`. Iterate
   `stepIR_sem` `n` times along `iterL`, following `wLoop`'s pattern and generalising the state
   at each step. Then `swapPs` swaps the bases and sets `w := min(2w, n)`
   (`minW_toWord`).
7. **`sortIR_sem`**. `loopK rCP rNP 64 passIR`: 64 iterations of `passIR_sem`, with `X p` the
   heap image of the current source (`X` at `memX`, `Y` at `memX + n`, alternating). Then apply
   `passes_ok` with `X 0 a = toWord (posL + 1 + entryOff L a)` from `walk_spec`. These values are
   injective because `entryOff` strictly increases (`entryOff_succ`, `qWords ≥ 5`) and stays
   below `2^64`. The result after 64 passes is back in `X`, since 64 is even.
8. **Pitfalls** (journal items 5, 12, 14):
   - generalise the state before any case analysis on `semXIR`;
   - no `rfl` between `XIR` terms with different `seq` association;
   - loads need `regs ≤ address`;
   - `simp only` with explicit dischargers for `rd_set_*`;
   - `BitVec.ofNat_add` in place of `toWord_add_one` on `1#64`.

---

## Part 6: the machine–model simulation of the sort (step 2), and the sorted log index

**Delivered: `FRXSortSim`** extended to 809 lines (675 code, 50 theorems). `ext`, `computes`,
the costs and every other module are unchanged.

- **The relation.**
  - `Regs M S D n w σ`: the registers `rI, rIE, rJ, rJE, rKk` hold `toWord` of `σ`'s indices, and
    `rW2, rN, rSrc, rDst` hold `w, n, S, D`.
  - `Rel S D n w src M σ`: `Inv M`, `Regs`, the heap holds `src a` at `S + a` and `σ.dst a` at
    `D + a` for `a < n`, and `Bnd n σ` (`i ≤ iE ≤ n`, `j ≤ jE ≤ n`).
  - `Lay S D n w sz`: `regs ≤ S, D`; the two ranges are disjoint, inside the memory and below
    `2^64`; `3n + 2 < 2^64`; `w ≤ n + 1`; and `0 < w` when `0 < n`.
  - `Lo P` (no store, no loop, register destinations) with `hframe`: such code leaves every cell
    `≥ regs` alone. This is the heap frame that `FRXDsl.frame` (registers only) does not give.
- **One step.** `stepIR` is split as `blockIR ; flagsIR ; chooseIR ; advIR ; tailIR` (`stepIR_eq`,
  by `rfl`).
  - `blockIR_sem`: `Regs` goes to `Regs (bstart n w σ)`. It uses `eqW_toWord`, `bW_and` and
    `minP_toWord`.
  - `choose_sem`: `rF = bW (takeL (keyLt I) src τ)`. It uses `ltW_toWord` and `cmpIR_sem`; the
    address hypotheses come from `regs ≤ S`.
  - `adv_blk`: `rAd := S + h` and the head is advanced.
  - `tail_sem`: the load of `src h`, then `rAd := D + k`, `k++`, and the store through
    `rd_storeM`. The heap changes at `D + k` only; the source is untouched because the ranges
    are disjoint.
  - **`stepIR_sem`**:

    ```lean
    theorem stepIR_sem (I : Array Word) (s : St) {S D n w : ℕ} {src : ℕ → Word} {σ : MS}
        (hL : Lay S D n w s.M.size) (hR : Rel S D n w src s.M σ) (hk : σ.k < n) :
        Rel S D n w src (semXIR I stepIR s).M (mstep (keyLt I) src n w σ) ∧
          (mstep (keyLt I) src n w σ).k = σ.k + 1
    ```

    No sortedness of `src` is needed. The bounds are carried by `Bnd` and `bstart_props`: after
    `bstart`, a head is available.
- **One pass.** `stepLoop`: `m` iterations of the step loop run `mrun`. The counter's decrement
  keeps `Rel` (`Rel.set`, `Rel.decS`). **`passIR_sem`**: from `rSrc = S`, `rDst = D`, `rW2 = w`,
  `rN = n` and tape word `posL = n`, a pass leaves the following:
  - `D + a` holds `passF (keyLt I) (S + ·) n w (D + ·) a` for `a < n`;
  - `rSrc = D` and `rDst = S`;
  - `rW2 = min(2w, n)` and `rN = n`.
- **The sort.** **`sortIR_sem`**:

  ```lean
  theorem sortIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {n : ℕ}
      (hn : I.getD posL 0 = toWord n) (hn2 : n < 2 ^ 62) (hsz : memX + n + n ≤ s.M.size)
      (hinj : ∀ a b, a < n → b < n → rd s.M (memX + a) = rd s.M (memX + b) → a = b) :
      (∀ a b, a < b → b < n → keyLt I (rd M' (memX + a)) (rd M' (memX + b)) = true) ∧
      (∀ a < n, ∃ c < n, rd M' (memX + a) = rd s.M (memX + c)) ∧
      (∀ c < n, ∃ a < n, rd M' (memX + a) = rd s.M (memX + c))
  ```

  Here `M'` stands for `(semXIR I sortIR s).M`; the Lean statement writes it out. The proof:
  - the pass invariant runs over `iterL` (`iterL_succ'`), with bases `baseX n p` (`X` on even
    passes, `Y = X + n` on odd ones) and widths `wseq n p` (`wseq_le`, `wseq_pos`);
  - the loop count is 64 (`entryK64`);
  - then `passes_ok` applies. 64 is even, so the result is back in `X`.
- **The log index.** **`logIR_sorted`** holds on a domain tape of a SNARK proof, given
  `memX + 2|L| ≤ |M|`. After `logIR`, `X[0..|L|)` is strictly sorted by `keyLt`, and as a set it is
  exactly `{posL + 1 + entryOff L k | k < |L|}`. These are the tape positions of the log's entries
  (`walk_spec`). Injectivity comes from `entryOff_lt`: `qWords ≥ 5`, and every position is below
  `2^64`, by `tape_entries_end`.
- **Controls.**
  - `Lo`: positive `lo_blockIR`, `lo_cmpIR`, `lo_chooseIR`; negative `not_lo_store`,
    `not_lo_heap`.
  - `baseX_ctl`: `X` on pass 0, `Y` on pass 1.
  - `Rel` is established on a real state inside `passIR_sem` (its positive control). `Lay` holds
    for every pass of the sort (`hLay` in `sortIR_sem`).
- **Checks.**
  - **Axioms.** `stepIR_sem`, `passIR_sem`, `sortIR_sem` and `logIR_sorted` depend on
    `propext, Classical.choice, Quot.sound`.
  - **Source rule.** 63 files, 0 findings. No `sorry`.
  - **Sequential profile** (`taskset -c 0`, `-DElab.async=false`;
    `logs/S-H2/FRXSortSim.profile`, `.time`):

    | wall | max RSS | type checking | simp | tactic execution |
    |---|---|---|---|---|
    | 27.1 s | 2.65 GB | 2.43 s | 7.7 s | 6.5 s |

**Notes for the next agent** (journal item 18):

- `rfl` and `assumption` can time out in `whnf` on goals such as `0 = toWord 0` when the context
  holds tape facts (`I.getD posL 0 = …`). Close such goals with explicit `exact h`, or put `rfl`
  last.
- A `let`-bound base function (`B p := if p % 2 = 0 …`) made `rw` time out in its closing `rfl`.
  Use a top-level `def` (`baseX`) and a rewrite lemma (`baseX_two`).
- In `(by …)` arguments that span several lines, separate tactics with `;`.
- A tactic argument whose implicit arguments are not yet determined (`rd_readAt … (by …)` without
  `pos :=`, or `hframe I _ s (by simp …)`) fails with "simp made no progress". Give the implicit
  arguments.

**What remains** (in order):

1. **Lookup.** A binary search over `X` (a `loopK` of 64) for the lower bound of `(a, ·)` in key
   order. Its specification follows from `logIR_sorted`. Positions increase with the entry index,
   so the first `X` slot whose answer is `a` holds the first entry of `L` with answer `a`. The
   pure half needs a tape lemma: the four answer words at `aposW I (posL + 1 + entryOff L k)` are
   `packBytes L[k].2`. The comparison with `FRMerkle`/`FRLog`'s first-preimage reading comes after
   that lemma. The program must be added to `logIR`/`ext` with its cost within Part 2's budget:
   the binary search is in the constant term.
2. Phases 3–6 and the SNARK case of `ext_good_tape`, as in Part 2.

**Stopped here** on the token budget. The state is commit-ready:

- every `FRX*` module builds;
- no `sorry`;
- the source rule is clean;
- `ext`, `computes` and the costs are unchanged.

---

## Part 7: the lookup (first preimage by binary search), in `ext`

**Delivered.**

- `FRXLog`: the lookup program, now part of `logIR`.
- `FRXLookup` (new): its semantics and its specification against `FRLog.ansIdx`.
- `FRXSortSim`: `logIR_sorted` is renamed **`idxIR_sorted`**. Its statement is unchanged; it is
  now about `idxIR := walkIR ; sortIR`.

**The program** (`FRXLog`).

- `lookIR` reads `n` from tape word `posL` and runs `loopK 64 bsBody`, then `foundIR`. `bsBody`
  is one halving step of the lower-bound search on `[lo, lo + len)`:
  - it probes `mid = lo + len/2` and loads `X[mid]`;
  - `ansLtIR` sets `rF := ansW(X[mid]) <_lex (rQ0 … rQ3)`;
  - then either `lo := mid + 1`, `len -= len/2 + 1`, or `len := len/2`;
  - it does nothing when `len = 0`.
- `foundIR` sets `rFd := [lo < n] ∧ ansW(X[lo]) = (rQ0 … rQ3)`.
- `lookCIR` loads the statement digest `c` (tape words `0 … 3`) into `rQ0 … rQ3` and runs
  `lookIR`. This is the first use of the lookup and the entry point I assumed for the
  first-preimage walks. If phase 3 starts its walks from another digest, only the four reads
  change.
- `logIR := idxIR ; lookCIR`. New registers `rQ0 … rQ3, rLo, rLn, rHf, rMd, rCB, rNB, rFd` are
  `106 … 116`.

**Cost and obligations (re-proved).**

- `cost_logIR : cost logIR t = 9095 + ⌊t/5⌋ · 11871`. The constant was 2,592; the lookup adds
  6,503. The per-word term is unchanged.
- `decOk_logIR` is re-proved:
  - `safe_logIR` has the new `seq` shape; the lookup has no `loopT`;
  - `wf_logIR`, `outs_logIR = 0` and `sizeIR_logIR ≤ 2^19` still hold.
- `computes` and `ext_caps` re-check unchanged. `ext`'s SNARK branch runs the lookup.
- The constant term stays far inside Part 2's budget: 9,095 against `≈ 2^47.58` left for
  phases 2–5.

**The specification** (`FRXLookup`).

- **The tape.**
  - `tape_answer`: the answer words of entry `k` are `packBytes L[k].2`.
  - `ansW_entry`: `ansW I (posE L k) = packBytes L[k].2`, where `ansW` is the first four key words
    and `keyW_eq : keyW = ansW ++ [x]`.
  - `packBytes_digest_inj`: `packBytes` is injective on digests.
  - `lexW_append`: the key order is the answer order, then the position order.
- **The pure search.**
  - `bsStep`/`bsRun`, with the invariant `BsInv` and `bsStep_inv`/`bsRun_inv`.
  - **`bsRun_spec`**: on a predicate that holds on a prefix of `[0, n)` with `n < 2^64`,
    64 halvings from `(0, n)` end at the prefix's length.
- **`lookup_pure`**: take a sorted index (`Sorted`: `idxIR_sorted`'s three facts) and the
  predicate `ltT` ("the answer at slot `a` is below `packBytes t`").
  - `ltT` holds on a prefix of the slots.
  - If `ansIdx L t = some k`, the prefix's end `b` is a slot (`b < |L|`) with
    `X[b] = posE L k`. This is the first entry of `L` with answer `t`. The proof: an equal answer
    at an earlier slot would be an entry with a smaller position, hence a smaller index,
    contradicting `findIdx?`.
  - If `ansIdx L t = none`, no slot has answer `t`.
- **The machine.**
  - `ansLtIR_sem`, `bsBody_sem` (one machine step is `bsStep (ltT I X T)`), `bsLoop`,
    `foundIR_sem`.
  - **`lookIR_sem`**: for a target `T` in `rQ0 … rQ3`:
    - `rLo = (bsRun (ltT I X T) 64 (0, n)).1`;
    - `rFd = [lo < n ∧ ansW(X[lo]) = T]`;
    - the heap is unchanged.
- **`logIR_lookup`** (`lookup_spec` for `c`). The setting is a domain tape of a SNARK proof, with
  `memX + 2|L| ≤ |M|`. After `logIR`:
  - if `ansIdx L c = some k`, then `rFd = 1` and `rLo = b` for a slot `b < |L|` with
    `X[b] = posE L k`;
  - if `ansIdx L c = none`, then `rFd = 0`;
  - and `X` is still `Sorted`.

  For any other target, `lookIR_sem` combined with `lookup_pure` gives the same result.
- **Controls.**
  - `bsRun_ctl`, by kernel `decide` on a 10-element toy: on a prefix predicate the search finds
    the prefix's end (3); on a predicate that is not a prefix (true only at 7) it returns 0. So
    the monotonicity hypothesis of `bsRun_spec` is needed.
  - `lookup_pure`'s two cases are the positive and negative controls of `ltT`/`Sorted`.
- **Checks.**
  - **Axioms.** `logIR_lookup`, `lookIR_sem`, `lookup_pure`, `decOk_logIR` and `computes` depend
    on `propext, Classical.choice, Quot.sound`.
  - **Source rule.** 64 files, 0 findings. No `sorry`.
  - **Sequential profile** (`taskset -c 0`, `-DElab.async=false`, `logs/S-H2/*.profile`):

    | Module | wall | max RSS | type checking | simp |
    |---|---|---|---|---|
    | `FRXLookup` (938 lines, 792 code, 52 theorems) | 33.6 s | 2.66 GB | 2.56 s | 11.1 s |
    | `FRXLog` (333 lines, 218 code) | 18.6 s | 2.60 GB | 0.79 s | 4.8 s |

**Notes** (journal item 19):

- `rw [ansW_eq]` also rewrote inside the `getD` terms it produces, and the following `simp` timed
  out. A separate lemma (`decide_ansW`, by `match` on the 4-list) avoids this.
- `(by revert hq; decide)` fails when `hq` mentions a free variable. Use a closed fact,
  `(by decide : ∀ r ∈ [..], P r) q hq`.
- Give implicit arguments that a `by` argument depends on: `bsRun_le (n := n)`, and `hHE (memX + a)`.
- The control `bsRun_ctl` needs `decide +kernel`; plain `decide` exceeds the recursion depth.

**What remains:**

1. **Phase 3, the ladder read.** It runs first-preimage walks from the caps (`lookIR` gives each
   step's first preimage), and the column store must equal `colL`'s first-preimage reading
   (`read_spec`). It depends on S-G2's `final`/`colL` interface.
2. Phases 4–6 and the SNARK case of `ext_good_tape`, as in Part 2.

**Stopped here** on the token budget. The state is commit-ready:

- every `FRX*` module builds (`FRXLookup`, `FRXSpec`, `FRXExt`);
- no `sorry`;
- the source rule is clean;
- `computes` re-checks with the new `cost_logIR`.

---

## Part 8: the lookup made parametric; handover for phase 3

The coordinator's answer was that the first-preimage walks do not start from `c`. They start from
the cap-0 entries absorbed in π's cap field (A.3/A.4). This part acts on that.

- **`FRXLog`.** The lookup of `c` (`lookCIR`) is removed. `logIR := idxIR` (walk and sort) again,
  and `cost_logIR` is back to `2592 + ⌊t/5⌋ · 11871`.
  - `lookIR` remains as a routine the later phases call with their own target in `rQ0 … rQ3`.
  - Its cost is `cost lookIR t = 6486`, evaluated in a scratch file outside the entry (`#eval`).
  - `decOk_logIR`, `computes` and `ext_caps` re-check.
- **`FRXLookup`.** `logIR_lookup` (for `c`) is replaced by **`idx_lookup`**, which is parametric in
  the target `t`. Take any state `s₂` whose `X[0..|L|)` is the one `idxIR` left and whose
  `rQ0 … rQ3` hold `packBytes t`. Then `lookIR`:
  - sets `rFd = 1` and `rLo = b` with `X[b] = posE L k` when `ansIdx L t = some k`;
  - sets `rFd = 0` when `ansIdx L t = none`;
  - and leaves `X` sorted.

  `readsC`, `tape_c` and `list4` were removed with `lookCIR`.
- **Checks.**
  - **Axioms.** `idx_lookup` and `computes` depend on `propext, Classical.choice, Quot.sound`.
  - **Source rule.** 65 files, 0 findings. No `sorry`.
  - `FRXLookup` is 902 lines (762 code, 48 theorems). `FRXLog` is 331 lines (214 code).

**Handover: phase 3, the ladder read.** It was not started: this agent's context is long. What the
next agent needs:

1. **Cap entries.** Read π's cap field from the tape (A.3/A.4): 512 cap-0 digests, each packed in
   4 words at a fixed offset of π's region (tape words `5 …`). Load each into `rQ0 … rQ3` with
   `input` from the computed offset; `readsC`'s pattern, removed in this part, did the same for
   tape words 0–3.
2. **The walk.** For each cap entry, do `lookIR`. `rFd = 1` gives `rLo = b` and `X[b]` = the
   entry's tape position (`idx_lookup`). Its query is the node query
   (`FRTranscriptDefs.nodeQ`/`frEnc`), and the children's digests sit in the query at fixed
   offsets. Continue with those children down to the column leaves, a loop over depth with
   lookups.
   - **Cost.** Each lookup is 6,486 steps, so 512 × depth × 6,486 is about `2^22 ·` depth,
     plus the reads. This goes into the constant term, which has `≈ 2^47.58` available
     (Part 2).
   - **Missing entries.** A missing entry (`rFd = 0`) must leave a defined value, as
     `colL`'s reading does with its default.
3. **`read_spec`.** The column store must equal `FRMerkle`'s `colL (frEnc 0)`, as used by S-G's
   soundness (`wordOf`, `colL_take`). The proof per step is `idx_lookup` plus `FR.Snd.ansIdx`'s
   definition (the first preimage), which is the reading `colL` uses.
4. **Phases 4–5**: the agreement set, then the butterfly inverse NTT equal to `coeffsAt`
   via `decode_row_D`.

**Stopped here.** This agent's context is long. The state is commit-ready:

- every `FRX*` module builds;
- no `sorry`;
- the source rule is clean;
- `ext`'s SNARK branch is walk and sort, as at Part 6, with the proved lookup routine available.

---

## Part 9: the ladder read of level 0 (phase 3), in `ext`; `read_spec` against `colL (frEnc 0)`

**Delivered.**

- `FRXReadDefs` (new): the read program `readIR sib np`, its cost and obligations, the facts
  about the tape it uses, and `decRead := logIR ; read0`.
- `FRXRead` (new): its semantics, **`read_spec`** and **`read_spec_F`**, and controls.
- `FRXExt`: `decSnark := decRead`. `ext` now runs the log index and then the read on every
  SNARK proof. `computes`, `ext_caps` and `ext_encode` re-check, and so do `FRXSpec`'s kernel toy
  runs.

**The program** (`FRXReadDefs`; registers `117 … 135`). For each position `p < np`
(`read0 := readIR 9 (2^18)`, `P30` level 0), it does five things:

1. It loads cap entry `p >> sib` from π's `cap₀` field into `rQ0 … rQ3` (tape word
   `capW0 + 4 (p >> sib)`, `capW0 = 2401`).
2. It walks down `sib` levels, from height `sib` to `1` (`loopK`, the counter is the height). At
   each step:
   - `lookIR` finds the digest's first preimage;
   - the node test is `|q| = 72` and query word 0 `= tagNW`;
   - the child at `X + 2 + 4 · bit_h(p)` goes into `rQ0 … rQ3`;
   - a missing entry or a failed test sets `rOk := 0`.
3. At the leaf: `lookIR`, then the column test (`7 < |q|` and word 0 `= tagCW`). On success
   `rQe := |q|`, else `0`.
4. It copies 128 words to `colBase + 128 p + w` (`colBase = 2^25`). Each word is masked
   branch-free to `[8 (w + 1) < rQe] · tape[X + 2 + w]`, so a failed read stores zeros.
5. It sets `p += 1`.

The store fills `[2^25, 2^26)`, below the log index at `memX = 2^26`.

**Cost and obligations.**

- `cost_read0 : cost read0 t = 18,001,952,782` (`≈ 2^34.07`): `2^18` positions, each with 10
  lookups of 6,486 steps (`cost_lookIR`) and a 128-word copy. It is a constant.
- `decOk_decRead` proves:
  - `wf` (`wf_readIR`, with `lookIR_nw`: the lookup writes no register `≥ 117`);
  - `safe`: the read has no `loopT` (`noLoopT_readIR`);
  - `cost`: `2592 + ⌊t/5⌋·11871 + 18,001,952,783 ≤ decBudget t`;
  - `outs = 0`;
  - `size = 294 + 570 + 1` (`sizeIR_logIR_eq`, `sizeIR_read0`).
- **Budget.** About `2^47.58 − 2^34.07` of the constant term is left for phases 4–6.

**Pure facts** (`FRXReadDefs`).

- Aligned slices of packed bytes: `packBytes_getD`, `packBytes_drop8`, `packBytes_take8`,
  `bytesAt_toList`, `packBytes_bytesAt`.
- The parsers on words: `ofLE_inj` and `tagWord_iff`, then
  - **`nodeChk_iff`**: `(|q| = 72 ∧ word₀ = tagNW) ↔ (take 8 = tagNode 0 ∧ |q| = 72)`;
  - **`colChk_iff`**: `(7 < |q| ∧ word₀ = tagCW) ↔ take 8 = tagCol 0`. The length test is
    needed: `tagCol 0` ends in two zero bytes, so a 6-byte `"FRMCOL"` would pack to the same
    word.
  - `packBytes_col`: the column's words are the query's words from word 1 on.
- The tape:
  - `tape_query`: query word `j` of entry `k` is at `posE L k + 1 + j`;
  - `tape_cap`: cap entry `e < 512` is at `capW0 + 4e`, with `capPi π e := bytesAt π (capOff + 32e) 32`
    and `capOff = fieldOff fCaps = 19,168` (`capOff_eq`).
- `pre_eq_ansIdx`: `FRMerkle.pre L d` is the entry at `FRLog.ansIdx L d`.

**The semantics** (`FRXRead`).

- `look_spec`: the lookup on any sorted index `Xi` (`Sorted`), with the frames it keeps (the
  heap, registers `≥ 117`).
- `LoK`/`hframeK`: the heap frame of store-free code that has counted loops.
- `capLd_sem`, `getIR_sem`, `nodeChk_sem`, `colChk_sem`, `child_sem`, `ld4_sem`: the blocks.
- `nodeFlag`/`colFlag`: the machine's tests are `parseNode 0`/`parseCol 0`. `child_words`: the
  child's four tape words are its packed digest.
- `nodeStepP` and **`colL_succ`**: one step of `colL (frEnc 0)` as a function of the digest.
  **`nodeBody_sem`**: one machine step is `nodeStepP`.
- `WalkSt`, `nodeWalk`, **`nodeLoop`**: `sib` steps keep this invariant: "`rOk = 1` and
  `rQ = packBytes d` with `colL d₀ sib p = colL d h p`", or "`rOk = 0` and `colL d₀ sib p = none`".
- `cpW_entry`, **`colIR_sem`**: the leaf leaves `rXq`, `rQe` such that the copy's words are
  `colWord (colL …)`.
- `copyBody_sem`, `copyLoop`, `copyIR_sem`: the copy.
- **`posBody_sem`**: one position.
- `posLoop`, **`readIR_sem`**: all positions; the index is kept.
- **`read_spec`**:

  ```lean
  theorem read_spec (c π L) (hD : Dom c π L) (s : St) (hM : Inv s.M)
      (hsz : memX + L.length + L.length ≤ s.M.size) {q w : ℕ} (hq : q < 2 ^ 18) (hw : w < 128) :
      rd (semXIR (tp c π L) (.seq idxIR read0) s).M (colBase + 128 * q + w) =
        colWord (colL (frEnc 0) L (capPi π (q / 2 ^ 9)) 9 q) w
  ```

  `Dom` bundles the domain hypotheses of `computes` (`|π| = piSize`, queries under `2^64`
  bytes, the tape within `2^64` words). `colWord o w` is word `w` of `packBytes col`, and `0`
  for `none`.
- **`read_spec_F`**: read as `F` elements (`rdF`, two words), the store is S-G's reading:

  ```lean
  rdF M (colBase + 128 * q + 2 * r) =
    ((colL (frEnc 0) L (capPi π (q / 2 ^ 9)) 9 q).map fun col => F.ofBytes (bytesAt col (16 * r) 16)).getD 0
  ```

  This is `FR.Snd.wordOf .N30 L es 0 r q` (`readF col o := F.ofBytes (bytesAt col o 16)`,
  `colOf` at `lvl _ 0 = ⟨6, 18, 290, 9⟩`), with the cap entries taken from π and not from the
  log. It relies on `b64_ofBytes_word` and `F_ofBytes_words`: an `F` read off bytes is its two
  packed words.

**Controls** (`FRXRead.ReadControls`, kernel `decide`, toy logs):

| Control | Kind | Shows |
|---|---|---|
| `nodeStepP_toy` | positive | bit `h` of `p` picks the left or right child |
| `nodeStepP_toy_none` | negative | a digest with no preimage, and a node query of level 1 (the level byte is checked), give `none` |
| `colWord_toy` | positive | the stored words of a 9-byte column are bytes `1…8`, then `9`, then `0` |
| `colWord_toy_none` | negative | a subtree with no preimage stores zeros; a level-1 column is not read at level 0 |
| `not_loK_store` | negative | `LoK` excludes stores |
| `nodeChk_iff`, `colChk_iff` | characterisation | the machine's tests are exactly the parsers (both directions) |
| `capOff_eq`, `tagNW_eq`, `tagCW_eq` | value | the cap field's offset (A.3) and the tag words |

**Checks.**

- **Axioms.** `read_spec`, `read_spec_F`, `readIR_sem`, `nodeBody_sem`, `colIR_sem`,
  `decOk_decRead`, `computes`, `ext_caps` and `ext_encode` depend on
  `propext, Classical.choice, Quot.sound`.
- **Source rule.** 67 files, 0 findings. No `sorry`. The only warnings are the
  `if_pos`/`if_neg` deprecations that other modules also have.
- **Build.** `lake build FRXReadDefs FRXRead FRXExt FRXSpec` takes 29.3 s (`logs/S-H2/build9.log`).
- **Sequential profile** (`taskset -c 0`, `-DElab.async=false`; `logs/S-H2/*.profile`, `*.time`):

  | Module | total / code / theorems | wall | max RSS | type checking | simp | tactics |
  |---|---|---|---|---|---|---|
  | `FRXReadDefs` | 428 / 286 / 36 | 15.5 s | 2.62 GB | 1.22 s | 4.8 s | 0.66 s |
  | `FRXRead` | 1,328 / 1,116 / 71 | 53.1 s | 2.80 GB | 5.23 s | 5.5 s | 30.1 s |
  | `FRXExt` | 36 / 11 / 3 | 5.7 s | 2.57 GB | 0 s | — | — |

  In `FRXRead`, most of the tactic time is about ten `show rd (entryK …) … = …` steps at about
  1.4 s each, plus one 6.5 s `obtain`. These are golf candidates: name the entry state with a
  `def`.

**Deviations from the blueprint.**

1. **A walk per position, not per subtree.** Each position walks from its cap entry: `2^18 × 10`
   lookups, `≈ 2^34.07` steps, against §6.3's `2^30` for "memory, index, ladder read". This is
   negligible against the `≈ 2^47.58` left, and the proof follows `colL`'s recursion one step at
   a time. Every one of the `2^18` positions is read: the word `W⁽⁰⁾` is indexed by position, as
   `wordOf` is.
2. **Cap entries from π, not from the log.** The read takes cap entry `e` from π's `cap₀` field
   (`capPi`). S-G's `wordOf` takes it from the absorb's message (`capDig es 0 e`). The link
   `capPi π e = capDig es 0 e` for `e < 512` is a hypothesis for the SNARK case of
   `ext_good_tape`: the verifier absorbs π's `cap₀` field at phase 2 (A.4, A.5). With it,
   `read_spec_F` is `wordOf .N30 L es 0` by unfolding.
3. **Only level 0, and only `P30`.**
   - `readIR` is parametric in `sib` and `np`. `readIR_sem` holds for `sib < 64`,
     `np ≤ 2^18` and `np ≤ 512 · 2^sib`.
   - The tag words, the cap offset and the 128-word columns are those of level 0.
   - The `L32` kind (`'L'`: `sib = 11`, `2^20` positions) needs `2^27` store words, more than
     `memX = 2^26`. See Q1.

**Open questions.**

- **Q1 (`L32` and the leaves).** §6.2 step 1 says `'L'`/`'P'` output `0 ‖ s ‖ n` at the parse,
  but `s` is in the committed witness, so a leaf needs the decoder too. For `'L'` (`m = 32`), the
  level-0 store does not fit under `memX = 2^26`. Two options:
  - raise `memX`: memory costs one step per word, so `2^28` is cheap, but every `FRX*` proof
    that uses `memX = 2^26` must be re-checked;
  - read and decode only the rows that hold `s`.

  Which does the coordinator want?
- **Q2 (the cap link).** Does S-G2's `final` (or `reassemble`) supply `capPi π e = capDig es 0 e`?
  Equivalently: `msgAt es (capPos 0)` is the first `16,384` bytes of π's field `fCaps`.

**Phase 5, the pure half** (`FRXDecodeB`, new: 162 lines, 98 code, 11 theorems; 7.2 s wall,
type checking 0.10 s, `logs/S-H2/FRXDecodeB.profile`).

- `bflyLevel`/`bflyRun`: the bottom-up, in-place butterfly. Level `l` merges adjacent blocks of
  `2^l` with `α = Ŵ_l(pt (s₀ + base))`; `ℓ` levels make `O(ℓ · 2^ℓ)` butterflies. This is the
  form a machine runs.
- **`bflyRun_block`**: after `l` levels, block `b` holds `coeffsAt pt N l (s₀ + b·2^l)` of its
  values. Hence **`bflyRun_eq`** (`= coeffsAt` on `[0, 2^ℓ)`) and `bflyRun_coeffs`
  (`= coeffsOfValues`).
- **`bfly_decode_D`**: through `decode_row_D`, the butterflies on `interpF D J u` return the
  message `c` when `u` agrees with `Enc(c)` on `J`, `|J| = 2^ℓ`.
- `firstK n A k`: the first `k` positions of `A` below `n`, the scan a machine makes. Its facts
  are `firstK_subset`, `firstK_lt` and `firstK_card`.
  **`decode_agree`**: if `u` agrees with `Enc(c)` on a set `A` of at least `2^ℓ` positions
  below `n ≤ 2^20`, the butterflies on `interpF D (firstK n A 2^ℓ) u` return `c` (§6.2 step 4,
  `P = A[0…k)`).
- Controls:
  - `bflyRun_one` (positive): one level is the explicit merge;
  - `bflyRun_zero`: zero levels are the identity;
  - `firstK_ctl` (`decide`): the first two of `{5, 1, 3}` are `{1, 3}`, and asking for 7 gives
    only 3, so `decode_agree` needs `2^ℓ ≤ |A|`.
- Axioms: `propext, Classical.choice, Quot.sound`.
- `FRXDecodeB` is not yet on `ext`'s import path. The machine program for the butterflies is
  the next step. Its simulation needs:
  - the table `wRow D 20 v` on the machine (one `invF` per row, from `FRXField`);
  - `wAt` as XOR sums over the bits of the block offset;
  - `mulF`/`addF` per butterfly.

  The proof then follows `bflyRun` level by level, as `passIR_sem` followed `passF`.

**What remains** (in order):

1. **Levels 1–4.** The same read with the level byte `i`, 16-row (32-word) columns and the
   caps at `capOff + 16384 + 8192 (i − 1)`. It is needed for the agreement set, which compares
   level `i`'s word with the encoding of level `i + 1`'s fold.
2. **Phase 4, the agreement set.** It depends on the K-fold and on `Enc` of the next level's
   decoded message (§6.2 step 4). So the decoder runs from level 4 (the final message, π's row
   13) up to level 0.
3. **Phase 5 on the machine**: the butterfly program, simulated against `bflyRun` (the pure
   half above is done).
4. **Phase 6, the output, and the SNARK case of `ext_good_tape`.**

**Stopped here.** Phase 3 and the pure half of phases 4–5 are complete. The state is
commit-ready:

- every `FRX*` module builds;
- no `sorry`;
- the source rule is clean.
