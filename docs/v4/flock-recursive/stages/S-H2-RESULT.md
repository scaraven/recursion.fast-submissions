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

---

## Part 10: the leaf branch (after the coordinator's answers to Part 9's Q1 and Q2)

The coordinator's answers:

- **Q1.** Leaves do not decode. The chain start `s` is in the leaf proof's clear header, at bytes
  `16 … 47`. S-0's `finSh` reads it as `bnd`, and the circuit pins the chain's start to that
  value. So `memX` stays `2^26`; only `'N'` decodes.
- **Q2.** On an accepted run, the cap absorb's query bytes are π's cap field. So `final`
  supplies `capPi π e = capDig es 0 e`. It goes in as a hypothesis of the SNARK case of
  `ext_good_tape`.

**Delivered.**

- `FRXReadDefs`: the SNARK branch is now **`decLN := kindIR ; ite rKN decRead leafIR`**.
  - `kindIR` sets `rKN := [byte₀ = 'N']` and `rKL := [byte₀ = 'L']`, from tape word 5.
  - `leafIR` outputs `0`, tape words `7 … 10` (header bytes `16 … 47`), then `2^18` (`'L'`) or
    `2^16` (`'P'`). That is `witWords (.leaf s (leafN k))`.
  - `decOk_decLN` proves `wf`, `safe` and `cost` (`max(cost decRead, 32) + 16` within
    `decBudget`), `outs ≤ 6` and the size.
- `FRXExt`: `decSnark := decLN`. `computes` re-checks, and so do `FRXSpec`'s `E_W`, `E_bad`,
  `ext_encode` and its toy runs.
- `FRXLeaf` (new; 160 lines, 129 code, 7 theorems):
  - `kindIR_regs`, `leafIR_out`;
  - `tape_leafS`: the chain start's packed words are tape words `7 … 10`;
  - `leaf_byte`, `lowByte_eq`;
  - **`run_leaf`**: on a domain tape of a leaf proof (`kindOf π = .snark k`, `k ≠ N30`), `ext`
    halts within the fuel with output `witWords (.leaf (bytesAt π 16 32) (leafN k))`;
  - **`E_leaf`**: under the same hypotheses, `E c π L = some (.leaf (bytesAt π 16 32) (leafN k))`.
    This is the leaf case of `ext_good_tape`. The `Rel` side (`chainEnd s n = h`, `c = leafStmt h n`)
    is `final`'s, from `leaf_sound` and the statement check.
- **`n`.** The program outputs `leafN k = 2^(m − 14)` and does not read `n` from `stmt`'s
  unaligned `enc64 n` (bytes 81–88). The verifier checks that the statement carries this `n`
  (§1.1, "checked"), so on an accepted proof the two are equal.

**Checks.**

- **Axioms.** `E_leaf`, `run_leaf`, `decOk_decLN` and `computes` depend on
  `propext, Classical.choice, Quot.sound`.
- **Source rule.** 69 files, 0 findings. No `sorry`.
- **Build.** `lake build FRXReadDefs FRXRead FRXExt FRXSpec FRXLeaf FRXDecodeB` takes 37.1 s
  (`logs/S-H2/build10.log`).
- **Profile.** `FRXLeaf` takes 10.1 s wall, with type checking 0.44 s and `simp` 2.5 s
  (`logs/S-H2/FRXLeaf.profile`).

**Controls.**

- `E_leaf` is the positive control: every leaf proof is extracted.
- The negative side is that `E_leaf` excludes `N30` (`hkn`); for `'N'` the branch runs the
  decoder path (`read_spec`).
- A kernel toy run of the SNARK branch is not possible: it needs a tape with `|π| = piSize`.

**What remains** (the coordinator's list, items 2–6). This agent's context is long, so it
stopped here. The state is commit-ready.

2. **The butterfly program on the machine**, simulated against `bflyRun` (`FRXDecodeB`). It
   needs:
   - `wRow D 20 v` computed on the machine (`invF` once per row);
   - `wAt` as XOR sums over the set bits of the block offset;
   - `mulF`/`addF` per butterfly, on `F` in two heap words (`rdF`).

   The proof is level by level, as `passIR_sem` was against `passF`.
3. **The agreement set on the machine**: a scan of positions `0 … 2^18 − 1` with a running
   count. It matches `firstK` (`decode_agree`).
4. **Levels 1–4**: the read with level byte `i` (generalise `tagNW`/`tagCW`, `capOff`, the
   32-word columns), then `Enc` and the K-folds of §6.2 step 4, decoding from level 4 up.
5. **Phase 6**: the node's `decodeWit` output.
6. **The SNARK `'N'` case of `ext_good_tape`.** Its hypotheses are:
   - `capPi π e = capDig es 0 e` for `e < 512` (Q2);
   - `ligerito_final`'s closeness and agreement.

   The leaf case is `E_leaf`.

---

## Part 11: the butterflies and the agreement scan on the machine (items 2–3); analysis of 4–6

**Delivered.** Items 2 and 3 of Part 10's list are complete and kernel-checked. Items 4–6 are not
started: the analysis in §4 shows that they need two decisions first (Q1, Q2).

### 1. Files (code lines by the core's `scripts/loc.py`)

| File | total / code / theorems | What |
|---|---|---|
| `FRXBflyDefs` (new) | 222 / 138 / 13 | the programs: heap `F` load/store (`ldF`, `stF`); `alphaIR`; `pairBody`, `levelIR ℓ`, `bflyIR ℓ tb`; the basis table `wtabIR tb` (`row0IR`, `rowIR`); `WF`, `NoLoopT`, `outs`, exact costs |
| `FRXBfly` (new) | 1,531 / 1,396 / 50 | the semantics, up to `bflyIR_sem`, `wtabIR_sem`, `bflyIR_decode` |
| `FRXAgree` (new) | 391 / 319 / 14 | the scan `scanIR`, `scanIR_sem`, `firstK_scan`, `scan_decode`, controls |
| `FRXSpec`, `FRXLeaf` | unchanged statements | repaired after upstream drift (below) |

**Upstream drift.** HEAD moved from `fd836c3` to `eba6537` during this part. S-0's commit `3aaa778`
changed `FRFormat.kindOf` to read `byteAt? π 0`, and `FRXSpec`/`FRXLeaf` stopped building. The
repair adds the `@[simp]` lemma `byteAt?_eq` to the seven `kindOf` simps. No statement changed.

### 2. What is proved

**Layout.** A row of `2^ℓ` `F` elements from cell `A` holds element `i` in cells `A + 2i`, `A + 2i + 1`
(`rdF`, `c₀` first). The basis table holds `(wRow D 20 v).getD i 0` at `tb + 40v + 2i`
(`v, i < 20`, 800 cells). Registers `140 … 184`.

**The basis table** (`wtabIR_sem`). On any state with `regs ≤ tb`, `tb + 800 ≤ |M|`:

```lean
(∀ v < 20, ∀ i < 20, rdF (semXIR I (wtabIR tb) s).M (tb + 40 * v + 2 * i) =
    (wRow D logNMax v).getD i 0) ∧
(∀ x, regs ≤ x → (x < tb ∨ tb + 800 ≤ x) → rd (semXIR I (wtabIR tb) s).M x = rd s.M x) ∧ Inv … ∧ size …
```

- Row 0 is `D(2^i)`: the words `(2^i, 0)`, because `D 0 = 0` and `D 1 = 1` (`wRow_zero_getD`).
- Row `v + 1` is LCH's `a (a + 1) · (b (b + 1))⁻¹`, with `b` entry `v + 1` of row `v`
  (`wRow_succ_getD`; `a − 1 = a + 1` and `x / y = x y⁻¹` hold by `rfl` in `F`). The program uses
  one `invF` per row.

**`α`** (`alphaIR_sem`). `α` is computed branch-free: `α = Σ_{i<20} [bit_i(base)] · T i` on the
table row at `rTr` (`mask = 0 − bit`, `mask_bit`, `rdF_acc`). With `T = wRow D 20 l` this is
`wAt D 20 l base` by definition.

**One butterfly** (`pairBody_sem`). Take pair `q` of level `l`, with `P = 2^l`,
`lo = ⌊q/P⌋·2P + q mod P` and `hi = lo + P` (`loP`, `hiP`; the machine uses `divu`, `remu`,
`mul`).

- The heap elements `u` at `lo` and `w` at `hi` become `u + α (w + u)` and `w + u`.
- Nothing else on the heap changes, and `q` advances.
- In characteristic 2 these are `bflyLevel`'s `u − α (w − u)` and `w − u` (`bflyLevel_lo`,
  `bflyLevel_hi`, by `rfl` on `F`'s `Sub`).

**A level** (`levelIR_sem`) and **the iteration** (`bflyIR_sem`).

- Each level is one loop over the `2^(ℓ−1)` pairs.
- The loop invariant is "element `i` is `bflyLevel … i` if `pairOf l i < q`, else unchanged".
  It rests on `pair_cases` (every position is its pair's low or high one), `pairOf_lt` and
  `hiP_lt`.

```lean
theorem bflyIR_sem … (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ 20) (hA : regs ≤ A) (hA2 : A + 2 * 2 ^ ℓ + 1 < 2 ^ 64)
    (hsz : A + 2 * 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + 800 < 2 ^ 64)
    (hdisj : tb + 800 ≤ A ∨ A + 2 * 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < 20, ∀ i < 20, rdF s.M (tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hY : ∀ i < 2 ^ ℓ, rdF s.M (A + 2 * i) = Y i) :
    (∀ i < 2 ^ ℓ, rdF (semXIR I (bflyIR ℓ tb) s).M (A + 2 * i) = bflyRun (M := F) D logNMax 0 ℓ Y i) ∧
    (∀ x, regs ≤ x → (x < A ∨ A + 2 * 2 ^ ℓ ≤ x) → rd (semXIR I (bflyIR ℓ tb) s).M x = rd s.M x) ∧
    Inv (semXIR I (bflyIR ℓ tb) s).M
```

**`bflyIR_decode`** composes this with `bfly_decode_D`. Suppose the row holds `interpF D J u` on
`D[0, 2^ℓ)`, `u` agrees with `Enc(c)` on `J`, `|J| = 2^ℓ` and `J ⊆ [0, 2^20)`. Then the row ends
holding the message `c`.

**The agreement scan** (`scanIR_sem`, item 3). The set `A` is a flag array: word `f j` at `fb + j`.
The scan `scanIR n k fb lb` lists positions at `lb`. With `L = scanL n f` (the flagged positions
below `n`, increasing):

- the count register is `min(|L|, k)`;
- cell `lb + t` holds `L[t]` for `t < min(|L|, k)`;
- the heap outside `[lb, lb + k)` is kept.

`firstK_scan` proves that `firstK n A k` is the set of listed positions on flags that mark `A`.
`scan_decode` is `decode_agree` restated on the scanned list.

### 3. Costs (exact, `cost_*`), against the remaining budget

| Program | Cost | Note |
|---|---|---|
| `pairBody` | 738 | of which `α` 618: 20 masked bit steps |
| `bflyIR ℓ tb` | `14 + ℓ (741 · 2^(ℓ−1) + 23)` | `ℓ = 17`: 825,557,397 ≈ `2^29.62` per row; 64 rows ≈ `2^35.62` |
| `wtabIR tb` | 79,606 | once |
| `scanIR n k fb lb` | `16 + 32 n` | `n = 2^18`: ≈ `2^23` |

The constant term has `≈ 2^47.585` left after the read (Part 9). The level-0 butterflies use
`2^35.62` of it, so `2^47.584` remains. `decSnark` is unchanged (`decLN`): these programs are not
yet on `ext`'s path, so `decOk_decSnark` and `computes` are unchanged and re-checked.

### 4. Items 4–6: what the analysis found

**The level-0 agreement set does not suffice alone.** `final`'s closeness of the level-0 word
(`¬ farL`) gives a codeword family `V` agreeing jointly with the word on `≥ n₀ − e₀ = 3·2^16 ≥ k₀`
positions. It does not say which positions. The extractor must compute the positions, and from
level 0 alone it cannot: that would need an errors-and-erasures decoder (Berlekamp–Welch or Gao),
`≈ 2^42` products for 64 rows, over the budget, and a decoder proof of its own. The computable set
is §6.2's fold-consistency set:

`A_c⁽ⁱ⁾ = {j : fold_z(W⁽ⁱ⁾ column j) = Enc(f⁽ⁱ⁺¹⁾)[j]}`

It needs `f⁽ⁱ⁺¹⁾`, so the decoder runs from level 4 (the final message) up, as Part 9 planned.
Levels 1–4 cannot be skipped. Two pieces are missing from the blueprint:

1. **The fold challenges** (Q1). `fold_z` uses P1.i's sumcheck challenges `z`. They are log
   answers on the verifier's Fiat–Shamir chain, and `runLog` answers each query by the first
   entry with exactly that query (`Oracle.runLog`).
   - To learn `z`, the extractor must replay the chain from the seed (`"FRSEED0" ‖ vk ‖ c ‖ hdr`)
     to P1.4's last round, about 430 FS items. At each item it builds the query (tag ‖ previous
     answer ‖ message from π's field, A.3/A.4) and finds its first exact match in `L`.
   - That needs a second index of `L`, keyed by query: the existing one is keyed by answer, for
     the Merkle walks. A second sort costs another `≈ 2,374 t`, and the linear term then exceeds
     `fuel_per_word = 4096` (`2,374 t` for the first sort, out of `4,080 t` available).
   - Options:
     - (a) raise `fuel_per_word` to `2^13` (still `≤ 2^16 t` of `extractorBudget`; a `claim.json`
       change);
     - (b) a cheaper query index that I do not see under this cost model;
     - (c) a coordinator ruling that `final` supplies `z` some other way.
   - §6.2 does not list this step.
2. **No hidden disagreement** (Q2). `truthC` (`f⁽ⁱ⁺¹⁾ = fold_z(f⁽ⁱ⁾)`) and linearity give
   `A_c ⊇ jointAgree(W⁽ⁱ⁾, V⁽ⁱ⁾)`. Decoding from the first `kᵢ` positions of `A_c` is correct only
   if `A_c ⊆ jointAgree`: no position `j` with `δ_j = W⁽ⁱ⁾_j − V⁽ⁱ⁾_j ≠ 0` and
   `Σ_x eq(z, x) δ_j(x) = 0`.
   - A.10 has no doom for this event, `Hide_i`. Its probability is at most `eᵢ · ℓᵢ / |K|`
     (Schwartz–Zippel on the multilinear `δ_j` at `z`, union over the `≤ eᵢ` disagreeing
     positions); at level 0 that is `≤ 2^16 · 6 / 2^256`.
   - It needs a doom row at P1.i (S-G's territory, via `seq_bad_le` across the rounds), or a
     ruling that `final` supplies `A_c⁽ⁱ⁾ = jointAgree` for `i ≤ 4`.
   - With `¬ Hide_i`, `A_c = jointAgree` exactly, and `scan_decode` applies at every level by
     induction from level 4.

**The plan once Q1 and Q2 are settled** (each piece in the style of this part):

1. **Chain replay** (Q1).
2. **Reads of levels 1–4**: `readIR` with the level byte in `tagNW`/`tagCW`, cap offset
   `capOff + 16384 + 8192(i − 1)`, 32-word columns and `sib = 8, 6, 4, 3` (`P30`), with the store
   below `colBase`. Cost `≈ 2^32`.
3. **Folds and `Enc`**:
   - the `eq(z, ·)` table in `K`;
   - per position, `Σ_x eq(z, x) W_x[j]` (`mulK`);
   - `Enc(f⁽ⁱ⁺¹⁾)` at `nᵢ` positions, by the forward butterfly (the inverse of `bflyIR`) per coset,
     or naively for `i ≥ 1`;
   - the flags `[fold = Enc]`, then `scanIR`.
4. **Interpolation `interpF D J u`** on `D[0, kᵢ)`, barycentric per target `s`:
   - `d_t = D[s] + D[J_t] = D[s ⊕ J_t]` (`D_xor`);
   - `ℓ(s) = Π d_t`, `e_t = w_t d_t⁻¹` with the weights `w_t` precomputed;
   - per row, `ℓ(s) Σ_t y(J_t) e_t`;
   - `s ∈ J` handled by a membership flag (`interpF` there is `y(s)`).

   The pure lemma (barycentric form = `interpF` off `J`) is needed. Cost at level 0:
   `2^34 · (invF + 64 · ≈ 75)` ≈ `2^46.6` steps, the largest item, under `2^47.58`. Memory: the
   64 output rows fill `[2^24, 2^25)`, and `y(J_t)` is read in place from the column store.
5. **`bflyIR` per row** (done), and the reshape of `f⁽ⁱ⁾` into level `i + 1`'s message by the
   coordinate split (§2.2).
6. **The node output** (`decodeWit` format, §1.4, A.5, A.7) from `f⁽⁰⁾`'s chain and L cells; then
   **the `'N'` case of `ext_good_tape`**, with the hypotheses `capPi π e = capDig es 0 e`,
   `¬ farL` for each level, `truthC`, and Q2's.

### 5. Controls

| Control | Kind | Shows |
|---|---|---|
| `toyScan_two` (kernel run, `decide +kernel`) | positive | flags `0,5,0,7,7,0,1,0`, `k = 2`: the scan lists `1, 3`, count 2 (`firstK 8 {1,3,4,6} 2`) |
| `toyScan_six` (kernel run) | limit | `k = 6 > |A|`: the count is `|A| = 4` and later cells stay 0 (`min(|L|, k)`) |
| `bflyIR_sem`, `wtabIR_sem`, `scanIR_sem` | universal | stated for every state meeting the layout hypotheses; their instances are the run's states |
| `bflyRun_one`, `bflyRun_zero`, `firstK_ctl` (Part 9) | positive / negative | the pure targets these programs are proved against |
| `wRow_zero_getD`, `wRow_succ_getD` | value | the table rows are LCH's recursion on `D` |

A kernel toy run of `bflyIR` was not added. It would need kernel evaluation of `mulF` and of the
pure `bflyRun` on `F` (the S-H1 note puts a kernel `clmul` evaluation at ≈ 15 s per field
inverse). `bflyIR_sem` is the universal statement.

### 6. Checks

- **Axioms.** `bflyIR_sem`, `bflyIR_decode`, `wtabIR_sem`, `scanIR_sem`, `firstK_scan`,
  `computes`, `E_leaf` and `E_W` depend on `propext, Classical.choice, Quot.sound`. The toy runs
  depend on `propext, Quot.sound`.
- **Source rule.** 74 files, 0 findings. No `sorry`.
- **Build.** `lake build FRXReadDefs FRXRead FRXExt FRXSpec FRXLeaf FRXDecodeB FRXBflyDefs FRXBfly
  FRXAgree` takes 60.9 s (`logs/S-H2/build11.log`; this includes rebuilding the modules touched by
  the upstream drift).
- **Sequential profile** (`taskset -c 0`, `-DElab.async=false`; `logs/S-H2/*.profile`, `*.time`):

  | Module | wall | max RSS | type checking | simp | tactics |
  |---|---|---|---|---|---|
  | `FRXBflyDefs` | 13.7 s | 2.69 GB | 0.38 s | 5.4 s | 0.13 s |
  | `FRXBfly` | 62.0 s | 2.96 GB | 8.86 s | 16.1 s | 21.5 s |
  | `FRXAgree` | 35.7 s | 3.89 GB | 19.8 s (≈ 18 s the two toy runs) | 1.2 s | 7.0 s |
  | `FRXSpec` | 13.1 s | 2.69 GB | 2.24 s | 2.3 s | 1.0 s |
  | `FRXLeaf` | 9.7 s | 2.63 GB | 0.42 s | 2.3 s | 0.39 s |

  `FRXBfly` was 111 s until its 29 `show rd (entryK …) … = _` steps became `dsimp only`. The same
  change applies to `FRXRead`'s ten (Part 9's golf note).
- `rowIR_sem` needs `set_option maxRecDepth 8000`: the kernel recurses deeply on the
  554-statement `invF` list inside the program term.

### 7. Deviations

1. **A flattened pair loop.** The blueprint does not fix the loop shape. `loopK` charges its
   constant cap, so a nested block × offset loop would be charged `2^(ℓ−1) · 2^(ℓ−1)` per level.
   One loop over the pairs, with `divu`/`remu`, keeps the cost at `ℓ · 2^(ℓ−1)` butterflies.
2. **`α` recomputed per pair** (20 masked steps, 618 of the 738). It is simple to prove, and the
   cost, `2^35.6` for 64 rows, is negligible. Hoisting it per block is a later optimisation.
3. **Not on `ext`'s path yet.** The decoder pieces stay off `decSnark` until the interpolation and
   the folds exist. Wiring them in now would add cost and prove nothing.

### 8. Open questions

- **Q1 (the fold challenges; blocking item 4).** The folds need P1.i's challenges, so the extractor
  must replay the Fiat–Shamir chain. That needs a query-keyed index of `L`, a second sort of
  `≈ 2,374 t`, over the linear fuel term. Raise `fuel_per_word` to `2^13`? Or another source of
  `z`? §6.2 should list the step either way.
- **Q2 (no hidden disagreement; blocking item 6).** Add a doom `Hide_i` at P1.i (S-G), or have
  `final` supply `A_c⁽ⁱ⁾ ⊆ jointAgree(W⁽ⁱ⁾, decodeL i)` for `i ≤ 4`. Without it, decoding from
  the fold-consistency set is not correct on every accepted non-doomed chain.
- **Q3 (memory).** The level-0 interpolation's 64 output rows (`2^24` words), the levels 1–4
  stores (`≈ 2^21.3` words) and the scratch fit in `[256, 2^25)` below the column store. This
  holds only if `y(J_t)` is read in place. A larger `memX` would simplify the layout but re-checks
  every `FRX*` proof that uses `memX`.

**Stopped here.** Items 2–3 are complete, and items 4–6 wait on Q1 and Q2. The state is
commit-ready:

- every `FRX*` module builds;
- no `sorry`;
- the source rule is clean.

---

## Part 12: the new fuel (after the coordinator's answers to Part 11's Q1–Q3)

The coordinator's answers (BLUEPRINT §10, stage-review changes 14):

- **Q1.** `fuel_per_word` is now 8,192 (`claim.json`).
- **Q2.** `Hide_i` is in P1.i's doom, so `final` supplies `A_c⁽ⁱ⁾ = jointAgree⁽ⁱ⁾`. It goes in as a
  hypothesis of the `'N'` case.
- **Q3.** The column values are read in place.

**Delivered.**

- `FRXProg`: `fuelPerWord := 2^13`. With it:
  - `fuel t = 3·2^46 + 2^13 t`, which matches `claim.json` (`fuel_base = 211,106,232,532,992`);
  - `fuel_le_budget` holds against `2^48 + 2^16 t`.
- `FRXReadDefs`: `decOk_decRead` and `decOk_decLN` re-proved. The only change is the linear
  constant, `2^13 − 16 = 8176`.
- `computes`, `ext_caps` and `E_leaf` re-check. They depend on `propext, Classical.choice,
  Quot.sound`.
- The build (`FRXProg` … `FRXAgree`, everything downstream of `FRXProg` rebuilt) takes
  2 min 50 s (`logs/S-H2/build11b.log`).
- The linear budget is now `8,176 t`. The answer sort uses `≈ 2,374 t`, which leaves
  `≈ 5,800 t` for the query-keyed index.

**Handover** (the coordinator's items 1–6; this agent's context is long, so it stopped here).

1. **Query index and challenge replay.**
   - Sort the log entries by a key of their query. The existing `sortIR` is parametric only in the
     key comparison: `cmpIR` compares answer words. A second instance should compare the query
     words `1 … ⌈|q|/8⌉` lexicographically, with the length word first.
   - Then replay the chain by binary search, as `lookIR` does over the answer index, for the
     first entry whose query equals the query built from the previous answer and π's bytes
     (A.4's item table; `FRTranscriptDefs` gives tags and offsets).
   - Prove it against `Oracle.runLog`'s `L.find? (·.1 = q)`. The index must be stable, so that
     the first entry wins among equal queries, which is what `FRXMerge`'s stable merge gives.
   - Read only up to P1.4's last round. Read `z` with `kAt`/`coordAt` as S-G does.
2. **The barycentric interpolation**, per Part 11 §4 step 4, with the pure lemma
   "barycentric = `interpF` off `J`, `y(s)` on `J`". It reads `y(J_t)` in place from
   `colBase + 128·J_t + 2r`.
3. **Levels 1–4** (the `readIR` generalisation, Part 11 §4 step 2), then the folds, `Enc` and the
   flags feeding `scanIR`, bottom-up from level 4 (the final message from π).
4. **The `decodeWit` output.**
5. **The `'N'` case.** Its hypotheses are `capPi π e = capDig es 0 e`, `¬ farL` and `truthC` for
   every level, and `A_c⁽ⁱ⁾ = jointAgree⁽ⁱ⁾`.
6. **Wire into `decSnark`.** `bflyIR`, `wtabIR` and `scanIR` already have exact costs and `WF`,
   `NoLoopT` and `outs = 0` lemmas.

---

## Part 13: the fold challenges off the log (item 1), by a forward scan; the `vk` question

**Delivered.** Item 1 of Part 12's handover, in a different form from the one it proposed
(deviation 1), up to one open input: the seed block (Q1). Items 2–6 are not started.
`decSnark`, `ext`, `computes` and every existing module are unchanged; the new modules are not yet
on `ext`'s import path.

### 1. Files (code lines by the core's `scripts/loc.py`)

| File | total / code / theorems | What |
|---|---|---|
| `FRXChainDefs` (new) | 224 / 143 / 14 | the first-match chain `fmAns`, the forward scan `scanC`, **`scanC_fm`**, controls |
| `FRXChain` (new) | 257 / 158 / 19 | the program `chainIR N tab sd` (registers `190 … 211`, memory `[2^23, 2^23 + 2^12 + 2^11)`), `WF`, exact cost, size, `outs` |
| `FRXChainSem` (new) | 661 / 584 / 23 | the blocks of one word: `lenIR_sem`, `qryIR_sem`, `ansPs_sem`, `st4IR_sem`, `nextIR_sem`, `recIR_sem`, `lastIR_sem` |
| `FRXChainLoop` (new) | 781 / 678 / 26 | the invariant `Stat`, `TabOK`, the four word cases, `qry_loop`, **`entry_sem`**, **`scan_sem`**, `entriesAt_tape` |
| `FRXChainTop` (new) | 364 / 313 / 11 | `cnt_sem` (the word count, from every state), `storesIR_sem`, `TabW`, `SeedOK`, **`chainIR_sem`** |
| `FRXChainFlock` (new) | 264 / 182 / 19 | Flock's targets: `fsMsgs`, `fsQ`, `nRep = 425`, the table `chTab`, **`tabW_chTab`**, **`chain_spec`** |

### 2. Why a forward scan, not a second sort (deviation 1)

Part 12 proposed a second instance of the merge sort keyed on the query (length word, then the
words), then a binary search per Fiat–Shamir item. The cost model rules this out:

- A comparison of two queries costs up to the shorter query's length. `loopK`/`loopT` charge
  their cap, so a word-by-word comparison inside the merge step is charged `cap` per comparison:
  `64 passes · (t/5) · cap(t)`, quadratic in `t`.
- Keying on a bounded prefix (length, tag, state: 6 words) costs about the answer sort's
  `2,374·t`. But then equal-prefix entries (same state, different messages) form groups that
  must be scanned for the full match. A group can hold up to `t/5` entries, and on a bad log the
  same group can be scanned once per item: no affine bound.

The scan used instead runs **once over the log's words, in log order**, with the next target in
hand. At an entry whose query is the target of position `p`, it records the answer and moves to
`p + 1`. Every word costs a constant: `cost (wordIR N) t = 176`. The scan is
`chainIR = cntIR ; storesIR chB chTab ; sd ; start ; loopT (count = the log's words, cap t)`, and

```lean
theorem cost_chainIR (N t : ℕ) (tab : List Word) (sd : XIR) :
    cost (chainIR N tab sd) t = 34 + 9 * tab.length + cost sd t + t / 5 * 24 + t * 179
```

With `|chTab| = 1,704`, that is `≈ 15,370 + cost sd` constant and **`≈ 183.8·t`** linear, against
the `≈ 5,800·t` Part 12 left for a second index. `sizeIR (chainIR …) = 284 + 10·|tab| + sizeIR sd`.

Why it equals `runLog`'s first-match reading:

```lean
theorem scanC_fm {T : ℕ → Digest → ByteArray} {N : ℕ} {st₀ : Digest} {L : Log}
    (hT : ∀ p st, 0 < p → stateIn (T p st) = some st) (hS : ¬ StateHit L) :
    ScanInv T N st₀ L (scanC T N st₀ L)
-- ScanInv … x : x.2.2.length = x.1 ∧ x.1 ≤ N ∧ fmPrev … x.1 = some x.2.1 ∧
--   ∀ p < N, x.2.2[p]? = fmAns T st₀ L p
```

- `fmAns T st₀ L p` is the first-match chain: position `p`'s query is `T p a_{p−1}`, answered by
  `L.find? (·.1 = q)`, exactly `OProg.runLog`'s reading.
- Proof idea: a query that carries `a_{p−1}` as its state cannot be logged at or before the entry
  that answered `a_{p−1}`. That would be a `StateHit`, one of `Bad`'s four disjuncts, which
  `final` excludes. So the first entry with `p`'s target comes after the one found for `p − 1`.
- The proof is by `List.reverseRecOn` (`scanInv_snoc`).
- Controls (`decide +kernel`): `scan_toy` (positive), `scan_toy_hit` with `toy_stateHit`
  (negative: on a log with a state hit, `fmAns` answers position 1 and the scan does not, so the
  hypothesis is needed), `fm_toy_none` (the chain stops at an unanswered query).

### 3. The machine proof

- **The word step** (`wordIR N`).
  - At a length word: `rQw := ⌈w/8⌉` and `rMt := [w = tl]`.
  - At query word `j`: `rMt &&= [w = exW j]`, with `exW j` the header cell `hB + j` below `h`, else
    the tape word `o + j − h`. The header is the seed's 15 words, or later the tag word and the 4
    words of the previous answer. The tail is the message read in place from π's tape words.
  - At answer word `m`: a branch-free select into `rS_m` (`maskSel`).
  - After answer word 3, if `rMt` and `p < N` (`recIR`): store the answer at `ansB + 4p` and at
    `H[1…4]`, load the next target (`tl`, `o`, tag) from the table, and set `h := 5`.
- **The invariant** `Stat I T N M₀ x s`:
  - `p` is in `rPi`, and the answers found are at `ansB + 4q`;
  - when `p < N`, the current target's length is in `rTl` and its packed words are `exW`;
  - `h ≤ 16` and `o < 2^62`;
  - the heap outside `H` and the answers equals the loop's initial heap.
- **The four cases** `word_len`, `word_qry`, `word_ans`, `word_last` each preserve `Stat` (and
  `Keep`: `rPi, rTl, rTh, rTo` and the heap). `word_last` advances the scan state exactly when
  `p < N` and the flag is set. Its record case rebuilds the next target from the table
  (`TabOK`).
- **`entry_sem`**: `qWords e` iterations do `scanStep T N x e`. The flag is
  `[|q| = |T|] ∧ ∀ j < ⌈|q|/8⌉, word_j = exW j`, which is `q = T p st` by `eq_of_packBytes` (equal
  sizes and equal packed words give equal bytes). **`scan_sem`** iterates over the entries.
- **`chainIR_sem`**: on a domain tape of a SNARK proof, given `TabW` (the table realises the
  targets) and `SeedOK sd` (the seed block writes the seed's 15 words into `H`):
  - the answers at `ansB + 4q` are the scan's for `q < (scanC …).1`;
  - the heap outside `[chB, chEnd)` is kept.
- The count `cnt_sem` comes from a store-free walk, so it holds from **every** state. This is the
  form `Safe`'s `loopT` constructor needs for the bound `count ≤ t`, and it does not clobber the
  log index `X`.
- **Flock** (`FRXChainFlock`).
  - `fsMsgs` lists, per Fiat–Shamir position, the π range of the absorbed message. It is read off
    the phase table as `FRVIR.genPhase` asks (`phaseOff n f`, round `j` at `+ j·roundBytes`,
    `uni`, seed `hdr`).
  - `fsQ vk c π p st` is `seedQ` / `absorbQ` / `squeezeQ` on it.
  - Controls: `fsMsgs_length` (451), **`fsMsgs_items`** (the kinds and lengths are exactly
    `fsItems`, A.4), `fsMsgs_aligned` (every message is 8-byte aligned inside `piSize`), and
    `fsMsgs_ctl` (the seed is `hdr` `(0, 48)`, position 2 is `cap₀` at `19,168`, `16,384` bytes).
  - `nRep_ctl`: P1.4 starts at FS position 417 with 8 items, so `nRep = 425` covers every
    `sAt es i l`.
  - `tabW_chTab`: the table realises `fsQ` on every tape of a proof of `piSize` bytes (absorb words
    = tag, state, π's words at `5 + o/8`).

```lean
theorem chain_spec (vk c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (hS : ¬ StateHit L) {sd : XIR}
    (hsd : SeedOK sd (extractorInput c π L).toArray (fsQ vk c π 0 zeroD))
    (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) {p : ℕ} (hp : p < nRep) {a : Digest}
    (ha : fmAns (fsQ vk c π) zeroD L p = some a) {m : ℕ} (hm : m < 4) :
    rd (semXIR (extractorInput c π L).toArray (chainIR nRep chTab sd) s).M (ansB + 4 * p + m) =
      (packBytes a.toList).getD m 0
```

### 4. Checks

- **Axioms** (`logs/S-H2/axioms13.log`).
  - `chain_spec`, `chainIR_sem`, `scanC_fm`, `tabW_chTab` and `computes` depend on
    `propext, Classical.choice, Quot.sound`.
  - `fsMsgs_items` depends on `propext`, and `scan_toy_hit` on `propext, Quot.sound`.
- **Source rule**: 92 files, 0 findings. No `sorry`.
- **Build**: `lake build FRXChainFlock FRXExt FRXSpec FRXLeaf FRXAgree` takes 56.6 s
  (`logs/S-H2/build13.log`).
- **Sequential profile** (`taskset -c 0`, `-DElab.async=false`; `logs/S-H2/FRXChain*.profile`,
  `.time`):

  | Module | wall | max RSS | type checking | simp | tactics |
  |---|---|---|---|---|---|
  | `FRXChainDefs` | 7.9 s | 2.67 GB | 1.29 s | 0.13 s | 0.33 s |
  | `FRXChain` | 14.1 s | 2.61 GB | 0.36 s | 3.66 s | 0.18 s |
  | `FRXChainSem` | 18.9 s | 2.66 GB | 1.72 s | 3.71 s | 5.32 s |
  | `FRXChainLoop` | 16.7 s | 2.69 GB | 2.16 s | 2.19 s | 3.13 s |
  | `FRXChainTop` | 10.7 s | 2.63 GB | 1.02 s | 1.08 s | 1.43 s |
  | `FRXChainFlock` | 19.7 s | 3.81 GB | 12.4 s (9.8 s `fsMsgs_items`) | 0.11 s | 0.50 s |

### 5. Deviations

1. **A forward scan, not a query-keyed sort and binary search** (§2). It is cheaper (`≈ 184·t`
   against `≈ 2,374·t` plus an unbounded group scan) and its correctness needs `¬ StateHit L`,
   which `final` has (`¬ Bad L`). §6.2 should list the step as "replay the Fiat–Shamir chain by
   one forward pass over the log, `nRep = 425` items".
2. **`TabW`/`SeedOK` as interfaces.** `chainIR_sem` is stated for any table and seed block
   meeting them. Flock's table is proved (`tabW_chTab`); the seed block is not written (Q1).
3. **Memory** `[2^23, 2^23 + 2^12 + 2^11)`: the table, `H`, and 425 answers of 4 words. The
   constants are literals (`chB = 8388608`, …, `layout_eq`); see journal item 26 on `omega`.

### 6. Open questions

- **Q1 (`vk`; blocking the seed block, hence the wiring and the `'N'` case).** The chain starts at
  the seed `"FRSEED0" ‖ vk ‖ c ‖ hdr`. `E` takes no `vk` (V4-6, `Certificate.lean`:
  `secure : ∀ vk, KS … (S.V vk) S.E …`), so the extractor cannot build the seed query. No rule over
  the log recovers it soundly:
  - A seed with another `vk'` (and its whole chain) can be logged before the real one at no cost.
  - Its challenges need not satisfy the truths, since `V vk'` need not accept.
  - So "the first seed for `(c, hdr)`" or "the first complete chain" can follow the wrong chain.

  **Proposal**: an `'N'` proof carries `vk` in `hdr`'s `pub` field (bytes `16 … 47`, unused for
  `'N'`; §1.1), and `V` checks `pub = vk` for `'N'` (one `piField fHdr 16 32`, `input 0`,
  `assertEq`). The node circuit's child check then needs a matching equality (the child's seed
  payload elements 5–6 against the `vk` cells 0–1). This is S-0/S-E/P's territory.

  With it, `sd` reads `vk` from tape words `7 … 10` and builds the 15 seed words with byte
  shifts (`(S_{j−1} >> 8) | (S_j << 56)`). `SeedOK` then follows from an `ofLE` lemma. The rest
  of item 1 is done.
- **Q2 (the link to `es`).** `final` must supply, from `runLog_chain`, that the verifier's chain
  agrees with the first-match chain on the first `nRep` positions:
  `∀ p < nRep, fmAns (fsQ vk c π) zeroD L p = some (ansAt es p)`. With it, `sAt es i l` is the
  machine's `chK` of the answer words at `ansB + 4(phStart(25+5i) + 2l + 1)`. That needs the
  verifier's query list to be `fsQ` (`FRVIRSpec.queries_gen` against `fsMsgs`).
  `fsMsgs_items` already pins the kinds and lengths. Who proves the message ranges against `gen`:
  S-G2 or S-0?

### 7. What remains (Part 12's items 2–6, unchanged)

1. The seed block (after Q1). Then `chainIR` goes before `idxIR` in `decSnark`, with `Safe` from
   `cnt_sem` and `tape_count_le`.
2. The barycentric interpolation (Part 11 §4 step 4).
3. Levels 1–4 (the generalised `readIR`), the folds with `z` from `ansB`, `Enc` and the flags.
4. The `decodeWit` output.
5. The `'N'` case of `ext_good_tape`. Its hypotheses: `¬ farL`, `truthC` and `A_c = jointAgree`
   at every level, Q2's chain link, and `¬ StateHit L`. The cap link `capPi π e = capDig es 0 e`
   follows from Q2's link at position 2 (`fsMsgs_ctl`: its message is π's `cap₀` field).
6. The wiring into `decSnark`, re-checking `decOk`/`computes`.

**Stopped here.** Item 1 is complete except for the seed block, which waits on Q1. The state is
commit-ready:

- every `FRX*` module builds;
- no `sorry`;
- the source rule is clean;
- `ext`, `computes` and the costs are unchanged.

---

## Part 14: the seed block and `chainIR` on `ext`'s path; the barycentric interpolation (most of it); revision 3.12

**Delivered.**
- Item 1 is complete: the seed block, and `chainIR` wired before the log index in `decSnark`, with
  `DecOk` and `computes` re-checked.
- Item 2 (the barycentric interpolation) is done as far as the target loop:
  - the pure form `interpF = baryVal`;
  - the program, its well-formedness and its exact cost;
  - the semantics of the tables `DJ` and `W`, of one target's `E` row and of the coordinate loop.
  - Left: the target body, the target loop and the end-to-end `baryIR_sem` (§4).
- Items 3–6 are not started.
- The coordinator's revision 3.12 constants are applied in every `FRX*` module (§3). `FRVIRChain`
  (S-0's `fsQ_gen`) builds against them.

### 1. Files (code lines by the core's `scripts/loc.py`)

| File | total / code / theorems | What |
|---|---|---|
| `FRXSeed` (new) | 425 / 316 / 37 | `vkOf π` (header bytes 16–47); `packBytes_shift7` (the words of `t ‖ s`, `|t| = 7`); `tape_seed`, `seedVal_eq`; the program `seedIR` (15 blocks `sdW j`); **`seedOK_seedIR`**; controls `shift7_ctl` and `shift7_ctl_neg` |
| `FRXDec` (new) | 150 / 105 / 10 | `safe_cntIR`, **`safe_chainIR`**; `decN := chainIR nRep chTab seedIR ; decRead`; `decLN2`; **`decOk_decLN2`**; **`chain_dec`** |
| `FRXBaryDefs` (new) | 317 / 214 / 19 | `interpF_self`, **`interpF_bary`**, **`baryVal_eq`**; the program `baryIR` (`djIR`, `wtIR`, `sBody`, `eBody`, `cBody`, `aBody`, `yIR`); `wf_baryIR`, `noLoopT_baryIR`, `outs_baryIR`, **`cost_baryIR`** |
| `FRXBary` (new) | 1,363 / 1,250 / 36 | `loopK_run` (a generic loop invariant), `addrPs_sem`, `alphaD_sem`; `djBody_sem`, **`djIR_sem`**; `wInner_sem`, `wtBody_sem`, **`wtIR_sem`**; `eBody_sem`, **`eLoop_sem`**; `aBody_sem`, `aLoop_sem`, `cBody_sem`, **`cLoop_sem`** |
| `FRXExt` | changed | `decSnark := decLN2` |
| `FRXChain` | changed | `cntIR` re-associated as `(pre ; loopT) ; post`, the shape `Safe.loopT` needs. Same cost and size, and the proofs are unchanged. |
| `FRXChainSem` | changed | `mul_toWord` renamed `mulW_toWord`: it clashed with `FRXBfly`'s once both are imported |
| `FRXLeaf` | changed | `run_leaf` follows `decLN2`. A closing `rfl` became rewrites: the kernel hit deep recursion unfolding `semXIR` over the 1,888-word table (journal 27) |
| `FRXChainFlock`, `FRXReadDefs`, `FRXLog`, `FRXLogSpec`, `FRXLookup`, `FRXLeaf` | changed | revision 3.12 constants (§3) |

### 2. What is proved

**The seed** (`FRXSeed`). An `'N'` proof carries `vk` in header bytes 16–47, and `V` asserts it
(S-0). So the extractor takes `vkOf π := bytesAt π 16 32`.
- The seed's payload `vk ‖ c ‖ hdr` is 14 tape words (`sPos`): `vk` at 7–10, `c` at 0–3, `hdr`
  at 5–10.
- The 7-byte tag shifts everything by 7 bytes. Seed word `j` is
  `(j = 0 ? tag : S_{j−1} >> 8) + (S_j << 56)`, where `S₁₄ = 0` (`packBytes_shift7`; the two
  parts occupy disjoint bytes, so `+` is `|`).

```lean
theorem seedOK_seedIR (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) (st : Digest) :
    SeedOK seedIR (extractorInput c π L).toArray (fsQ (vkOf π) c π 0 st)
```

**The chain on `ext`'s path** (`FRXDec`).
- `decSnark := kindIR ; ite rKN decN leafIR`, with `decN := chainIR nRep chTab seedIR ; logIR ; read0`.
- `safe_chainIR` gives the bounds of both of the chain's loops on every SNARK tape:
  - the walk's count is `|L| ≤ t/5` (`tape_count_le`);
  - the scan's count is `cnt_sem`'s `wordsOf L`, which is `≤ t` (`wordsOf_le`: `posL + 1 +
    wordsOf L ≤ |tape|`).
- `decOk_decLN2` holds. `computes`, `ext_caps`, `E_leaf`, `E_W` and the toy runs re-check.
- The chain's memory `[2^23, 2^23 + 6,144)` lies below the column store (`2^25`) and the log
  index (above `memX = 2^26`).

```lean
theorem chain_dec … (hS : ¬ StateHit L) (st₀ : Digest) (s : St) (hM : Inv s.M)
    (hsz : chEnd ≤ s.M.size) {p : ℕ} (hp : p < nRep) {a : Digest}
    (ha : fmAns (fsQ (vkOf π) c π) st₀ L p = some a) {m : ℕ} (hm : m < 4) :
    rd (semXIR (extractorInput c π L).toArray (chainIR nRep chTab seedIR) s).M (ansB + 4 * p + m) =
      (packBytes a.toList).getD m 0
```

S-G2's `final` supplies `ha` with `st₀ = zeroD`. It also supplies `vkOf π = vk` from `V`'s
assertion, so `fsQ (vkOf π) = fsQ vk` is S-0's `fsQ_gen` query list.

**The barycentric interpolation, pure form** (`FRXBaryDefs`).
- `interpF_self`: on `J`, the value is returned (`pt` injective on `J`).
- `interpF_bary`: off `J`, `interpF pt J y s = ℓ(s) · Σ_{i∈J} y i · w_i (pt s − pt i)⁻¹`.
  Here `ℓ(s) = Π_{m∈J}(pt s − pt m)` and `w_i = (Π_{m∈J∖i}(pt i − pt m))⁻¹`.
- The machine's value over `F`, with `J` the scan's list `Jl` (`dj`, `wgt`, `ellS`, `eAt`), is
  `baryVal Jl k s y = (ℓ(s) = 0 ? y s : ℓ(s) Σ_t y(J_t) E_t)`:

```lean
theorem baryVal_eq {Jl : List ℕ} (hnd : Jl.Nodup) (hJ : ∀ j ∈ Jl, j < nMax) {s : ℕ}
    (hs : s < nMax) (y : ℕ → F) : baryVal Jl Jl.length s y = interpF D Jl.toFinset y s
```

`ℓ(s) = 0` iff `s ∈ J` (`D` injective below `2^20`). The machine therefore needs no membership
array.

**The program** `baryIR k C jb djb wb eb cb cs ob tb`.
- It works coordinate-wise over `F`: `C` coordinates per column, element `c` of position `j` at
  `cb + cs·j + 2c`. Level 0 has `C = 64` and `cs = 128`. Levels 1–4 have the 16 `F`-coordinates
  of 8 `K` elements.
- `djIR`: `DJ[t] := D(J_t)`, by `alphaIR` on the basis table's row 0 (`alpha_D`: the row-0 sum
  is `D x`, from `wAtD_eq`).
- `wtIR`: `W[t] := (Π_{m≠t}(DJ[t] + DJ[m]))⁻¹`.
- Per target `s` (`sBody`):
  - `D(s)`;
  - the `E` row `E[t] := W[t](D s + DJ[t])⁻¹` and `ℓ := Π_t(D s + DJ[t])` (`eBody`);
  - the flag `[ℓ = 0]`;
  - per coordinate (`cBody`): `acc := Σ_t y_c(J_t) E[t]` in registers (`aBody`, read-only), then
    `out[c][s] := (flag ? y_c(s) : ℓ · acc)` at `ob + 2k·c + 2s`.

**The semantics proved** (`FRXBary`). Each statement holds for every state meeting its layout
hypotheses:
- `djIR_sem`: `DJ[t] = D(J t)` for `t < k`, and the heap outside `DJ` is kept.
- `wtIR_sem`: `W[t] = (Π_{m<k}(m = t ? 1 : G t + G m))⁻¹`, and the heap outside `W` is kept.
- `eLoop_sem`: the `E` row and `ℓ`.
- `cLoop_sem`: `out[c][s₀] = (ℓ = 0 ? y_c(s₀) : ℓ Σ_t y_c(x t) E[t])` for every `c < C`, and the
  heap outside the `C` output cells is kept.
- Register frames are given in the form "every register the body does not write".

### 3. Revision 3.12 (the coordinator's list)

| Constant | Was | Now |
|---|---|---|
| `fsMsgs_length`, `fsMsgs_items` | 451 | **497** (`decide +kernel`, re-checked) |
| `fsMsgs_ctl` position 2 (`cap₀`) | `(19168, 16384)` | **`(22320, 16384)`** |
| `nRep` (P1.4 = phase 46 at FS 463, 8 items) | 425 | **471** (`nRep_ctl` re-checked; P1.i is phase `26 + 5i`) |
| `π.size` literals (`msgOk`, `FRXLog`, `FRXLogSpec`, `FRXLeaf`, `FRXLookup`, `FRXReadDefs`, `FRXSeed`) | 755,680 | **800,640** |
| `posL` | `5 + 94460` | **`5 + 100080`** |
| `capOff_eq`, `capW0_eq`, `tape_cap` | 19,168 / 2,401 / 2,396 | **22,320 / 2,795 / 2,790** |
| `chTab` length | 1,704 | **1,888** (`cost_decN` and `sizeIR_decN` now go through `nRep`) |

- **Columns** are 1,088 B at level 0 and 320 B at levels 1–4, with 48 zero bytes.
  - The read's parser checks only `7 < |q|` and the tag. The read copies the first 128 words.
  - `read_spec` is stated against S-0's `colL`, and it re-checks unchanged.
  - Levels 1–4 (item 3) must use S-0's 3.12 column layout.
- **Not done:** I did not build `FR` as a whole. Other tracks' modules are being fixed by the
  integration agent.

### 4. Costs (exact), against the budget

| Program | Cost | Note |
|---|---|---|
| `seedIR` | `≤ 376` | 15 blocks |
| `chainIR nRep chTab seedIR` | `34 + 9·1888 + cost seedIR + 24⌊t/5⌋ + 179t` | ≈ `17,400 + 183.8·t` |
| `decN` | `≤ 18,002·10^6 + 2,558·t` | the linear term is 2,558 of 8,176 |
| `baryIR k C …` | `38 + 2487k + 108kC + 1363k² + 106k²C` | the semantics of every loop are already proved against these programs |

- **Level 0** (`k = 2^17`, `C = 64`): `8,147 · 2^34 ≈ 2^46.99` steps. That leaves `≈ 2^46.0`
  of the constant `≈ 2^47.585`.
- **Level 1** (`k = 2^14`, `C = 16`): `≈ 2^29.6`.
- Part 11 estimated `2^46.6` for level 0. The actual figure is higher because `aBody` costs 106
  steps per coordinate per pair: it recomputes `J_t`'s column address and reloads `E[t]` in every
  coordinate.
  - The fix, if needed, is a precomputed column-address table.
  - It is not needed for the budget.

### 5. Checks

- **Axioms** (`logs/S-H2/axioms14.log`). These depend on `propext, Classical.choice,
  Quot.sound`: `computes`, `chain_dec`, `seedOK_seedIR`, `decOk_decLN2`, `baryVal_eq`,
  `djIR_sem`, `wtIR_sem`, `eLoop_sem`, `cLoop_sem`, `E_leaf`. `fsMsgs_items` depends on
  `propext` alone.
- **Source rule**: 106 files, 0 findings. No `sorry`.
- **Build** (`logs/S-H2/build14.log`): `lake build FRXSeed FRXDec FRXExt FRXSpec FRXLeaf FRXBary
  FRVIRChain` is green. The 3.12 rebuild from `FRXLog` down took 1 min 38 s.
- **Sequential profile** (`taskset -c 0`, `-DElab.async=false`; `logs/S-H2/FRX{Seed,Dec,BaryDefs,Bary}.{profile,time}`):

  | Module | wall | max RSS |
  |---|---|---|
  | `FRXSeed` | 13.2 s | 2.69 GB |
  | `FRXDec` | 7.4 s | 2.61 GB |
  | `FRXBaryDefs` | 12.0 s | 2.71 GB |
  | `FRXBary` | **91.4 s** | 2.90 GB |

  `FRXBary` is the largest. Its long proofs are step-by-step frame chains. The step lemmas could
  be shared, which would make it a golf candidate.

### 6. Controls

| Control | Kind | Shows |
|---|---|---|
| `shift7_ctl` (`decide +kernel`) | positive | word 1 of `t ‖ s` is `(S₀ >> 8) + (S₁ << 56)` |
| `shift7_ctl_neg` | negative | the unshifted payload word is not the seed word |
| `seedOK_seedIR`, `chain_dec` | universal | on every SNARK tape and every initial state |
| `interpF_self` / `interpF_bary` | the two branches | `baryVal_eq` uses both; `ℓ(s) = 0` iff `s ∈ J` |
| `fsMsgs_items`, `fsMsgs_ctl`, `nRep_ctl` | value | re-checked at 3.12 |

- There is no kernel toy run of `baryIR`: it would need kernel evaluation of `invF` (journal 24).
- `baryVal`'s own controls are the two pure lemmas.

### 7. Deviations

1. **`vkOf π` instead of `vk`.** The seed is built from π's header, as changes 16 provide. The
   link `vkOf π = vk` is `V`'s assertion, which S-G2 supplies.
2. **No membership array.** `s ∈ J` is decided by `ℓ(s) = 0`.
3. **Accumulators in registers.** The coordinate loop is outside the `t` loop, and the `E` row
   lives on the heap. Every inner loop is then read-only, which keeps the semantics simple.
4. `chain_spec`'s `zeroD` is an **auto-bound implicit**: `FRXChainFlock` does not import `FRVIR`.
   The theorem therefore holds for every initial state, which is harmless and more general.
   `chain_dec` names it `st₀`.

### 8. What remains (in order)

1. **Finish item 2** (`FRXBary`), from the delivered lemmas:
   - `sBody_sem`: `alphaD_sem` for `D(s)`, the copy into `fDs`, `eLoop_sem`, the flag lemma
     `XOp.eq.eval (a ||| b) 0 = bW (decide (⟨wB a, wB b⟩ = 0))`, `cLoop_sem`, then `s += 1`.
   - The target loop.
   - `baryIR_sem`, composing with `djIR_sem`, `wtIR_sem` and `baryVal_eq`: `out[c][s] = interpF
     D J y_c s`.
   - The layout `BaryLay` (bases, disjointness): `DJ`, `W`, `E` at `2^22 + {0, 2, 4}·2^18`; flags
     and `J` list at `2^21`; basis table at `2^20`; output rows at `2^24`.
2. Levels 1–4 (Part 12 item 3) with 3.12's padded 320-B columns. Then the `decodeWit` output, the
   `'N'` case and the wiring (items 4–6, unchanged).

**Stopped here.** The cause is context length. The state is commit-ready:
- every `FRX*` module and `FRVIRChain` build;
- no `sorry`;
- the source rule is clean.

---

## Part 15: the interpolation finished (`baryIR_sem`, level 0's layout); the read made per-level (levels 1–4)

**Delivered.**
- **Item 1 is complete.** It covers the target body, the target loop and the end-to-end
  `baryIR_sem`, with `out[c][s] = interpF D J y_c s`. Level 0's concrete layout is instantiated
  (`bary0_interp`).
- **Item 2 is started.** The first sub-step is done: the ladder read is generic in the level, and
  levels 1–4 have their `P30` instances, specs and costs. Three groups of statements are unchanged
  and re-check:
  - level 0's `read_spec`, `read_spec_F` and `cost_read0`;
  - `decOk_decLN2` and `computes`;
  - `E_leaf`.
- **Not started:** the folds, `Enc`, the flags, the per-level decode, the `decodeWit` output, the
  `'N'` case and the wiring (§7).

### 1. Files (code lines by the core's `scripts/loc.py`)

| File | total / code / theorems | What |
|---|---|---|
| `FRXBaryTop` (new) | 558 / 479 / 15 | `eqz_or` (the `[ℓ = 0]` flag on words); `wf_sBody`; **`sBody_sem`**; `BaryLay`, `cell_ne`, `sValM`, **`sLoop_sem`**; **`baryIR_sem`**, **`baryIR_interp`**; level 0's layout (`tb0 … ob0`, `bary0`, `lay0`, **`bary0_interp`**) |
| `FRXReadDefs` | 494 / 327 / 40 (was 479) | The program is parametric: `readIR i cw sb nw sib np` (level byte `i`, cap word `cw`, store base `sb`, `nw` words a column). Supporting changes: `tagNWl i`, `tagCWl i`, and `nodeChk_iff`/`colChk_iff`/`parseNode_eq_*` at level `i`. **`read0 := readIR 0 capW0 colBase 128 9 (2^18)`**, so `cost_read0` and `sizeIR_read0` are unchanged. |
| `FRXRead` | 1,351 / 1,139 / 71 (was 1,328) | Every lemma from `capLd_sem` to `readIR_sem` is generalised the same way. The cap is abstract: a function `cap` with the tape fact `hcap`. Level 0's `read_spec` is instantiated from it. |
| `FRXReadLv` (new) | 183 / 108 / 17 | Levels 1–4: `capOffL`, `capLogL`, `logNL`, `sibL`, `capPiL`, `capWL`, `stB`, `readLv`; `tape_capL`; **`readLv_spec`**, **`readLv_spec_F`**; `cost_readIR` (general), `cost_readLv`; controls |

### 2. What is proved

**One target** (`sBody_sem`). Take a state with `bS = s₀`, `s₀ < k`, `s₀ < 2^20`. On a layout with
its stated disjointness, the result holds for every `c < C`:

```lean
rdF (semXIR I (sBody k C jb djb wb eb cb cs ob tb) s).M (ob + 2 * k * c + 2 * s0) =
  if ∏ t ∈ range k, (D s0 + rdF s.M (djb + 2 * t)) = 0 then rdF s.M (cb + cs * s0 + 2 * c)
  else (∏ t ∈ range k, (D s0 + rdF s.M (djb + 2 * t))) *
    ∑ t ∈ range k, rdF s.M (cb + cs * x t + 2 * c) *
      (rdF s.M (wb + 2 * t) * (D s0 + rdF s.M (djb + 2 * t))⁻¹)
```

It also gives:
- `bS := s₀ + 1`;
- the heap outside the `E` row and the `C` output cells of `s₀` is kept.

The proof composes `alphaD_sem` (giving `D(s₀)`), the copy into `fDs`, `eLoop_sem`, the flag
block and `cLoop_sem`. The flag block rests on `eqz_or`:
`XOp.eq.eval (a ||| b) 0 = bW (decide (⟨wB a, wB b⟩ = 0))`.

**The layout** `BaryLay k C jb djb wb eb cb ob tb` is a linear order. From bottom to top:
1. the basis table's row 0;
2. `J`;
3. `DJ`, `W` and `E`;
4. the output rows (`2kC`);
5. the column store.

With this order every disjointness obligation is `omega`. Output cells of distinct targets are
distinct (`cell_ne`: `kc + s` is injective for `s < k`).

**The target loop** (`sLoop_sem`). Its invariant:
- `bS = j`;
- the cells of the targets `< j` hold `sValM`;
- the heap outside `E` and the output rows is kept.

**The program** (`baryIR_sem`). On `BaryLay`, with `k ≤ 2^20`, `J` at `jb` (entries below `2^20`)
and the basis table's row 0 at `tb`:

```lean
∀ s0 < k, ∀ c < C, rdF (semXIR I (baryIR k C jb djb wb eb cb cs ob tb) s).M
    (ob + 2 * k * c + 2 * s0) = baryVal Jl k s0 (fun j => rdF s.M (cb + cs * j + 2 * c))
```

Two further facts hold:
- the heap outside `[djb, eb + 2k) ∪ [ob, ob + 2kC)` is kept;
- `Inv` holds.

`baryIR_interp` composes this with `baryVal_eq`. For `k = |Jl|`, `Jl` without repeats, the result
is `interpF D Jl.toFinset y_c s0`.

**Level 0** (`bary0_interp`, `bary0 = baryIR (2^17) 64 jb0 djb0 wb0 eb0 colBase 128 ob0 tb0`). The
bases are:
- `tb0 = 2^20`, `jb0 = 2^21`;
- `djb0 = 2^22`, `wb0 = 2^22 + 2^19`, `eb0 = 2^22 + 2^20`;
- `ob0 = 2^24`, so row `c` is at `2^24 + 2^18 c`.

The column store is the read's (`colBase = 2^25`, 128 words a column). The interpolation keeps
the heap below `2^22`, the heap in `[eb0 + 2^18, 2^24)` and the heap from `2^25` on. That
includes the chain's answers (`[2^23, 2^23 + 6,144)`) and the log index (`memX`).

**The per-level read** (`FRXRead`, generalised in place). `posBody`, `posLoop` and `readIR_sem`
take an abstract cap `cap : ℕ → Digest` with `ncap` entries, through the tape fact

```lean
hcap : ∀ e < ncap, ∀ m < 4, (tp c π L).getD (cw + 4 * e + m) 0 = (packBytes (cap e).toList).getD m 0
```

They also take a store `sb + nw·np ≤ memX`. `readIR_sem` stores, at `sb + nw q + w`, word `w` of
`colL (frEnc i) L (cap (q / 2^sib)) sib q`. Level 0's `read_spec` is the instance `cap = capPi π`
(`tape_cap`). Levels 1–4 (`readLv_spec`, `readLv i = readIR i (capWL i) stB 32 (sibL i)
(2^(logNL i))`) are the instances `cap = capPiL i π`:

```lean
theorem readLv_spec_F … {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) {q r : ℕ} (hq : q < 2 ^ logNL i) (hr : r < 16) :
    rdF (semXIR (tp c π L) (readLv i) s).M (stB + 32 * q + 2 * r) =
      ((colL (frEnc i) L (capPiL i π (q / 2 ^ sibL i)) (sibL i) q).map
        fun col => F.ofBytes (bytesAt col (16 * r) 16)).getD 0
```

This is S-G's `wordOf κ L es i r q` with the cap entries read from π. The link
`capDig es i e = capPiL i π e` is Q2's chain link at the C phases (`capOffL_fsMsgs`).
- The 3.12 padding (48 zero bytes) is never copied: the read copies only the first 32 words of the
  304-byte column, which are the 16 `F` elements.
- The column parser still checks only `7 < |q|` and the tag.

### 3. Costs (exact), against the budget

| Program | Cost | Note |
|---|---|---|
| `readIR i cw sb nw sib np` | `14 + np (6,576 + 6,544 sib + 25 nw)` (`cost_readIR`) | level 0 (`np = 2^18`, `sib = 9`, `nw = 128`): `18,001,952,782`, `cost_read0` unchanged |
| `readLv 1 … 4` | 3,914,334,222; 764,149,774; 137,429,006; 27,656,206 (`cost_readLv`) | `≈ 2^32.17` in all |
| `bary0` | `8,147 · 2^34 + …` (Part 14) | `≈ 2^46.99`, unchanged |

- The four reads are `loopK` only, so the linear term is unchanged: `≈ 2,558·t` of `8,176·t`.
- The constant term has `≈ 2^46.0` left after level 0's interpolation (Part 14). It is `≈ 2^45.99`
  after the reads.
- Estimates for the rest of item 2. These are op counts, not yet `cost_*` lemmas:
  - folds, `≈ 2^31` (level 0: `2^18` positions × 64 rows × one `K × F` product);
  - `Enc` by the forward butterfly per coset, `≈ 2^32`;
  - the per-level interpolations and butterflies, `≈ 2^31`;
  - the scans, `≈ 2^23`.

  They total `≈ 2^33.5`, far inside the margin.

### 4. Controls

| Control | Kind | Shows |
|---|---|---|
| `nodeStepP_lv1` (`decide +kernel`) | positive / negative | A level-1 node query is a level-1 step. `toyN`'s level-0 query reads `none` at level 1: the level byte is checked at every level. |
| `nodeStepP_toy`, `nodeStepP_toy_none`, `colWord_toy*` | positive / negative | level 0, re-checked against the generalised program |
| `tagNWl_one_ne` | negative | the level-1 tag words differ from level 0's |
| `capOffL_fsMsgs` (`decide +kernel`) | value | `fsMsgs` at FS positions 359, 398, 425, 449 (`capPos 1 … 4`) absorbs π's `(capOffL i, 32·2^(capLogL i))` |
| `capOffL_ctl` | value | the offsets and `sibL = 9, 8, 6, 4, 3`; `capPiL 0 = capPi` |
| `eqz_or` | value | the flag word is `[ℓ = 0]` on both words of the `F` pair |
| `baryIR_sem`, `sLoop_sem`, `sBody_sem`, `readLv_spec` | universal | for every state meeting the layout hypotheses |

### 5. Checks

- **Axioms** (`logs/S-H2/axioms15.log`).
  - These depend on `propext, Classical.choice, Quot.sound`: `computes`, `E_leaf`, `read_spec`,
    `read_spec_F`, `readIR_sem`, `readLv_spec`, `readLv_spec_F`, `cost_readLv`, `sBody_sem`,
    `sLoop_sem`, `baryIR_sem`, `baryIR_interp`, `bary0_interp`, `decOk_decLN2`.
  - `eqz_or` and `nodeStepP_toy_none` depend on `propext, Quot.sound`. `capOffL_fsMsgs` depends on
    `propext`.
- **Source rule**: 109 files, 0 findings. No `sorry`.
- **Build**: green.
  - `lake build FRXReadLv FRXBaryTop FRXDec FRXExt FRXSpec FRXLeaf FRXAgree FRVIRChain` takes
    1 min 14 s (`logs/S-H2/build15.log`).
  - The rebuild from `FRXRead` down takes 1 min 54 s (`build15c.log`).
  - The final build is `build15e.log`.
- **Sequential profile** (`taskset -c 0`, `-DElab.async=false`;
  `logs/S-H2/FRX{BaryTop,ReadLv,Read}.{profile,time}`):

  | Module | wall | max RSS | type checking | tactics |
  |---|---|---|---|---|
  | `FRXBaryTop` | 28.9 s | 2.77 GB | 5.28 s | 11.2 s |
  | `FRXReadLv` | 8.5 s | 2.67 GB | 1.42 s | 0.37 s |
  | `FRXRead` (generalised) | 53.1 s | 2.81 GB | 5.42 s | 30.5 s |

  `FRXRead` took 53.1 s sequentially before the change (Part 9), so the generalisation costs
  nothing.

### 6. Deviations

1. **The read is generalised in place.** The alternative was a copy for levels 1–4.
   - `read0` is now an instance, and every downstream statement (`read_spec`, `cost_read0`,
     `decOk`) is unchanged.
   - The level-0 constants (`capW0`, `colBase`, 128, the tags) became parameters, and the cap
     became an abstract `cap` with its tape fact.
2. **The levels 1–4 store is `stB = 2^24`**, which is level 0's output-row region.
   - That region is free until level 0's interpolation, which runs last (bottom-up).
   - Level 1 needs `2^21` words.
3. **`BaryLay` is a linear order** rather than pairwise disjointness. Level 0's layout satisfies
   it (`lay0`), and so will the levels' layouts.
4. The frames of `sLoop_sem` and `baryIR_sem` are stated precisely, as `[djb, eb + 2k) ∪ [ob,
   ob + 2kC)`, not as one interval, so that the chain's answers between `E` and the output rows
   are visibly kept.

### 7. What remains (in order; the next agent's list)

1. **Item 2, continued** (bottom-up `i = 4, 3, 2, 1`, then level 0).
   - **The challenges.** `sAt es i l = kAt es (phStart (26 + 5i) + 2l + 1)`. The FS positions of
     P1.i are `347, 390, 417, 441, 463` (S-0's `pos-3.12.txt`), with `ℓ = 6` at level 0 and 4 at
     levels 1–4.
     - On the machine the answer words sit at `ansB + 4p` (`chain_dec`).
     - A lemma `rdK M (ansB + 4p) = chK a` from `packBytes a` is needed.
     - `final` supplies `fmAns … p = some (ansAt es p)` (Q2 of Part 13).
   - **The eq table.** `eqBits (sAt es i) ℓ r` for `r < 2^ℓ` in `K`, by doubling. Check `eqBits`'
     bit order in `FRSoundnessWeights` first.
   - **The fold.** `foldAt κ L es i j = Σ_r eqBits(s, ℓ, r) · W⁽ⁱ⁾[r][j]` is one `K × F` product
     per row (two `mulF`). `W⁽ⁱ⁾[r][j]` is at `stB + 32j + 2r` (`readLv_spec_F`), or at
     `colBase + 128j + 2r` at level 0.
   - **`Enc`.** `encAt κ i m j = encF (mLog κ i) m j`, the novel basis on `D`. Compute it by the
     forward butterfly per coset of size `kᵢ` (the inverse of `bflyIR`'s levels) on the two
     `F` coordinates of `K`, and prove it against `encF`.
   - **The message.** At level 4 it is `finalAt es x` (π's final field, 67,376, `2^7 · 32` B).
     Otherwise it is `nextMsg`'s reshape of level `i + 1`'s decoded rows: K element `x` from rows
     `2(x mod 8)`, `2(x mod 8) + 1`, column `x div 8`.
   - **The flags.** `fb[j] := [fold(j) = Enc(j)]`, then `scanIR nᵢ kᵢ fb jb`. `firstK_scan` gives
     the first `kᵢ` positions of `consSet`, which `final` makes `jointAgree` (`A_c = jointAgree`).
   - **The decode.** `baryIR kᵢ 16 …` (`C = 16`: the 16 `F` rows) on a `BaryLay` for level `i`.
     Then `bflyIR (mLog i)` per row gives `coeffsOfValuesD`, so the rows are `msgOf κ L es i r`.
   - Proposed memory:
     - the tables at `tb0`/`jb0`/`djb0`/`wb0`/`eb0`, reused with `kᵢ`;
     - the output rows at `2^22 + 2^21`;
     - the flags at `2^21 + 2^18`;
     - the current message at `2^23 + 2^16` (`2^19` words), above the chain's `chEnd`.
   - **Level 0 last.** Fold with `ℓ = 6`, `Enc₀(f⁽¹⁾)` on `2` cosets of `2^17`, then `scanIR 2^18
     2^17`, `bary0` (`bary0_interp`), and `bflyIR 17` on the 64 rows (`bflyIR_decode`).
2. **The `decodeWit` output** (§1.4, A.5, A.7), from `f⁽⁰⁾`'s rows.
3. **The `'N'` case of `ext_good_tape`.** Its hypotheses:
   - `vkOf π = vk`;
   - `¬ farL`, `truthC` and `consSet = jointAgree` at every level;
   - the chain link at positions `< nRep`, which also gives `capDig es i e = capPiL i π e` at
     `capPos i`;
   - `¬ StateHit L`.
4. **The wiring into `decSnark`**, re-checking `decOk`/`computes`.
   - Every new program is `loopK`-only, with exact costs.
   - Each still needs `WF`/`NoLoopT`/`outs` lemmas; the reads and `baryIR` have them.

**Stopped here.** The cause is context length. The state is commit-ready:
- every `FRX*` module builds, and `FRVIRChain` builds;
- no `sorry`;
- the source rule is clean;
- `ext`, `computes` and the costs on `ext`'s path are unchanged.

---

## Part 16: the level decode, pure (`level_decode`); `Enc` by the forward butterflies; the `eq` table on the machine

**Delivered.** This part covers the following pieces of Part 15 §7 item 1. The rest of item 1
and items 2–4 are not started (§7). `decSnark`, `ext`, `computes` and every existing statement
are unchanged; the new modules are not yet on `ext`'s import path.

- **The pure decode chain of one level**, from S-G's objects to the machine's `F` arithmetic:
  `level_decode`, `mem_consSet_iff` and `nextMsg_coords`.
- **`Enc`**: the forward butterflies, pure (`fwdRun_enc`) and on the machine (`fwdIR_enc`).
- **The challenges and the `eq` table**: `sAt_words` and `eqtIR_sem`.

### 1. Files (code lines by the core's `scripts/loc.py`)

| File | total / code / theorems | What |
|---|---|---|
| `FRXEncB` (new) | 181 / 131 / 7 | `fwdLevel`, `fwdRun`, `D_block`, `normW_block`, **`fwdRun_block`**, **`fwdRun_enc`**; controls `fwdRun_one`, `fwd_bfly_one` |
| `FRXLevel` (new) | 228 / 145 / 19 | K coordinates (`K_sum_f₀/₁`, `algebraMap_mul_K`, `ofF_add_u_mul`); **`chK_words`**, `rdK_of_words`; `foldAt_f₀/₁`, `encF_f₀/₁`, **`mem_consSet_iff`**, **`nextMsg_coords`**; `bflyRun_map`, `interpF_map`; `consN`, `wordN`; **`level_decode`**, **`msgOf_embed`** |
| `FRXFwd` (new) | 628 / 544 / 19 | the programs `farithIR`, `fpairBody`, `flevelIR`, `fPre`, `fStep`, **`fwdIR ℓ tb`**; `WF`, `NoLoopT`, `outs`, exact cost; `farith_sem`, `fpairBody_sem`, `flevelIR_sem`, `fPre_sem`, **`fwdIR_sem`**, **`fwdIR_enc`** |
| `FRXEqT` (new) | 600 / 502 / 20 | the programs `eqBody`, `eqEnt`, **`eqtIR ℓ cb eb`**; `WF`, `NoLoopT`, `outs`, exact cost; `bitPs_sem`, `eqBody_sem`, `eqEnt_sem`, **`eqtIR_sem`**, **`sAt_words`**; control `eqBits_ctl` |

The new code is 1,322 lines in total. The entry's code total was 36,791 at the start of this
part.

### 2. What is proved

**One level's decoding** (`FRXLevel.level_decode`). For `i < 5`, assume:
- `hfar : ¬ farL κ L es i`;
- `hA : consSet κ L es i = jointAgree (wordK κ L es i) (decodeL κ L es i)` (what `final` supplies,
  §10 changes 14).

Then, for every row `r` and every `x < 2^mLog`:

```lean
algebraMap F K (bflyRun (M := F) D logNMax 0 (mLog κ i)
    (interpF D (firstK (2 ^ (lvl κ i).logN) (consN κ L es i) (2 ^ mLog κ i)) (wordN κ L es i r))
    x) = msgOf κ L es i r x
```

The left side is exactly what the machine computes in `F`:
- the first `kᵢ` positions of `A_c` (`scanIR`, `firstK_scan`);
- the barycentric interpolation of the word's row (`baryIR_interp`);
- the butterflies (`bflyIR_sem`).

The proof has three steps:
- `exists_msg` and `msgOf_eq` (S-G's) give the codeword's message;
- `decode_agree` gives the decode over `K`;
- `bflyRun_map` and `interpF_map` bring it back to `F`.

`truthC` is not a hypothesis. The flags test `consSet` itself, so only `A_c = jointAgree` is
needed. `msgOf_embed` is the corollary that the decoded messages are `F`-valued.

**The flags in `F`** (`mem_consSet_iff`). `j ∈ consSet` iff two equalities hold:
- the fold's `f₀` equals `Enc` of the next message's `f₀` coordinates:
  `Σ_r W[r][j]·(eqBits s ℓ r).f₀ = encF mLog (f₀ ∘ nextMsg) j`;
- the same for `f₁`.

Both sides are what the machine computes:
- the fold is two `F` dot products of the column with the `eq` table's coordinates;
- the encoding is two `F` forward runs.

`nextMsg_coords`: below level 4, if level `i + 1`'s messages are `F`-valued, the next message's
K element `x` is the pair of rows `2(x mod 8)` and `2(x mod 8) + 1` at column `x div 8`. So the
two `F` rows to encode are read straight from level `i + 1`'s decoded rows.

**`Enc` by the forward butterflies** (`FRXEncB`). `fwdLevel l` maps a block's halves `u`, `w` to
`u + α w` and `u + α w + w`, with `α = Ŵ_l(D base)`. It is the inverse of `bflyLevel`
(control `fwd_bfly_one`). `fwdRun ℓ` applies the levels `ℓ − 1, …, 0`.
- `fwdRun_block`: block `b` of size `2^ℓ` ends holding
  `Σ_x A(b 2^ℓ + x) X_x(D(b 2^ℓ + j))`.
- `fwdRun_enc`: with a message of `2^m` coefficients zero-padded to `2^n` (`m ≤ n ≤ 20`),
  `fwdRun n A j = encF m c j` for every `j < 2^n`.

**On the machine** (`FRXFwd.fwdIR_sem`, `fwdIR_enc`). The hypotheses are `bflyIR_sem`'s: the row
at `rA0`, the basis table (`wtabIR`) at `tb`, and the same layout. Under them
`fwdIR ℓ tb` leaves `fwdRun ℓ Y`, and so `encF m c`, in the row, and keeps the heap outside it.

**The `eq` table** (`FRXEqT.eqtIR_sem`). The input is the challenges `S v` (`rdK`) at
`cb + 8v`, `v < ℓ`, with the challenges disjoint from the table. Then:
- `rdK` at `eb + 4x` is `eqBits S ℓ x` for every `x < 2^ℓ`;
- the heap outside `[eb, eb + 4·2^ℓ)` is kept.

Each entry is the defining product `∏_{v<ℓ} (bit_v x ? s_v : 1 − s_v)`. `1 − s` is computed as
`1 + s` on the words (`rdK_one_sub`), and the factor is chosen by `ite` on the bit.

`sAt_words` supplies the input. If the chain left `ansAt es p` at `ansB + 4p` for P1.i's
squeeze positions `p = phStart (26 + 5i) + 2v + 1`, then `rdK` at
`ansB + 4(phStart (26 + 5i) + 1) + 8v` is `sAt es i v`. `chK_words` reads a K element off an
answer's four packed words. The positions are symbolic, so revision 3.13's move does not touch
this code.

The bit order was checked: `eqBits r ℓ x` weighs bit `v` of `x` with `r_v`, little-endian, and
`foldAt` uses it as such. `eqBits_ctl` makes this concrete: row 1 of a 2-variable table is
`s₀(1 − s₁)` and row 2 is `(1 − s₀)s₁`.

### 3. Costs (exact), against the budget

| Program | Cost (`cost_*`) | Instances |
|---|---|---|
| `fwdIR ℓ tb` | `14 + ℓ (741 · 2^(ℓ−1) + 27)` | `ℓ = 18, 16, 14, 12, 10`: 1,748,238,836; 388,497,854; 84,984,200; 18,211,154; 3,794,204. Two rows (`f₀`, `f₁`) per level: `≈ 2^32.06` in all |
| `eqtIR ℓ cb eb` | `12 + 2^ℓ (63 + 271 ℓ)` | `ℓ = 6`: 108,108; `ℓ = 4`: 18,364 |

- Both programs are `loopK`-only, so the linear term is unchanged (`≈ 2,558·t` of `8,176·t`).
- The constant term still has `≈ 2^45.99` left; Enc takes `2^32.06` of it.
- Enc over a whole level costs `n log n / 2` butterflies, against `§6.3`'s naive `2^41.8`.

### 4. Controls

| Control | Kind | Shows |
|---|---|---|
| `fwdRun_one` | positive | one level on two points is `(u + α w, u + α w + w)` |
| `fwd_bfly_one` | inverse | the forward level undoes `bflyRun`'s on two points, so it is the inverse NTT's inverse, not a second inverse NTT |
| `eqBits_ctl` | value / bit order | `eqBits S 2 1 = S₀(1 − S₁)`, `eqBits S 2 2 = (1 − S₀)S₁` |
| `level_decode`, `mem_consSet_iff` | universal | for every log, transcript and level with the stated hypotheses; `not_farL_nil` (S-G) shows `¬ farL` is satisfiable |
| `fwdIR_sem`, `eqtIR_sem`, `eqEnt_sem` | universal | for every state meeting the layout hypotheses |

### 5. Checks

- **Build.** The worktree's S-0 modules are being edited by INT-2 (revision 3.13): `piSize` is
  now 797,888, and `FRSoundnessDefs` and my `FRXLog` (through `piSize_eq`) fail there
  (`logs/S-H2/build16.log`). The verification build therefore runs on a snapshot: `HEAD` plus the
  four new modules, in `logs/fr-build-SH2s`, log `logs/S-H2/build16s.log`.
  The snapshot build `lake build FRXEncB FRXFwd FRXLevel FRXEqT FRXReadLv FRXBaryTop FRXExt
  FRXSpec FRXLeaf FRXAgree FRXComputes` is green: 2,286 jobs in 3 min 56 s, rebuilding the entry
  from S-0's modules down.
- **Axioms** (`logs/S-H2/axioms16.log`):
  - `level_decode`, `msgOf_embed`, `mem_consSet_iff`, `nextMsg_coords`, `fwdRun_enc`,
    `fwdIR_sem`, `fwdIR_enc`, `eqtIR_sem`, `sAt_words`, `chK_words`, `fwd_bfly_one` and
    `eqBits_ctl` depend on `propext, Classical.choice, Quot.sound`;
  - `cost_fwdIR` and `cost_eqtIR` depend on `propext`.
- **Sequential profile** (`taskset -c 0`, `-DElab.async=false`;
  `logs/S-H2/FRX{EncB,Level,Fwd,EqT}.{profile,time}`):

  | Module | wall | max RSS | type checking |
  |---|---|---|---|
  | `FRXEncB` | 8.1 s | 2.66 GB | 0.37 s |
  | `FRXLevel` | 7.9 s | 2.72 GB | 0.22 s |
  | `FRXFwd` | 53.6 s | 2.82 GB | 4.47 s |
  | `FRXEqT` | 36.7 s | 2.79 GB | 2.38 s |
- **Source rule**: 115 files. The only finding is `FRVIRTplFast.lean:435` ("partial"), another
  track's module in progress. The new `FRX*` files have none, and no `sorry`.

### 6. Deviations

1. **One forward run per level, not per coset.** Part 15 §7 proposed `Enc` by the forward
   butterfly per coset of size `kᵢ`. Zero-padding the message to `nᵢ` and running all `logN`
   levels gives `Enc` at every position in one run (`fwdRun_enc`). There are no coset offsets
   (`α` stays `wAt D 20 l base`, so `alphaIR` and `pairPs` are reused unchanged). The cost is
   `logN/mLog` times the per-coset figure, `≈ 2^32` in all.
2. **The forward program is a copy of `FRXBfly`'s pair/level proofs**, not a parametrisation of
   them, so `bflyIR` and its statements are untouched. It adds 544 code lines; the generalised form
   would save ≈ 250.
3. **The `eq` table by the definition, not by doubling.** The doubling needs a `loopK` whose count
   (`2^v`) is below its cap. The DSL lemmas so far assume count = cap (`loopK_run`). The direct
   product costs `≤ 384` K products, which is negligible.
4. **`truthC` is not a hypothesis of the decode.** The handover listed it for the `'N'` case, but
   `level_decode` needs only `¬ farL` and `A_c = jointAgree`. It may still be needed for the
   output step (item 2) if `decodeWit`'s format is stated through `fTab`/`foldMsg`.

### 7. What remains (in order; the next agent's list)

1. **Item 1, continued**, now with the pure targets fixed:
   - **The fold and flag program** `flagIR`. Per position `j < nᵢ`:
     - `acc_c := Σ_r W[r][j]·E[r].f_c` (`W` at `cb + cs·j + 2r`, `E` at `eb + 4r + 2c`);
     - `flag := [acc₀ = enc₀[j] ∧ acc₁ = enc₁[j]]` at `fb + j`.

     Prove it against `mem_consSet_iff`. The inner loop is the `aLoop_sem` pattern; the outer
     loop is the `eqtIR_sem` pattern.
   - **The message rows**:
     - for `i < 4`, the copy of level `i + 1`'s decoded rows into two zero-padded `F` rows
       (`nextMsg_coords`: rows `2(x mod 8) + c`, column `x div 8`);
     - for `i = 4`, `finalAt`'s coordinates read from π's tape at C.4's offset (`fsMsgs` at
       position `nRep`, symbolic).
   - **The composition per level**:
     `eqtIR ; copy ; fwdIR (×2) ; flagIR ; scanIR ; baryIR k 16 ; bflyIR (×16)`, with one
     `BaryLay` per level and the conclusion `level_decode`.
   - **Level 0**: `ℓ = 6`, 64 rows, `bary0`, the column store at `colBase`.
2. **The `decodeWit` output** (§1.4, A.5, A.7), from `msgOf … 0` (`msgOf_embed`, S-G's
   `msgOf_F`/`fF`).
3. **The `'N'` case of `ext_good_tape`**, with these hypotheses:
   - `vkOf π = vk`;
   - `¬ farL` and `consSet = jointAgree` per level;
   - the chain link (`fmAns … p = some (ansAt es p)` for `p < nRep`), which feeds `sAt_words`;
   - `capDig es i e = capPiL i π e`;
   - `¬ StateHit L`.
4. **The wiring into `decSnark`**: `WF`, `NoLoopT` and `outs` exist for `fwdIR` and `eqtIR`.
5. **Revision 3.13** (when INT-2 lands with the coordinator's list):
   - the existing constants: `nRep` (P1.4's end moves), `chTab`/`fsMsgs` (re-derived), and the
     `capW0`/`capOffL` and `piSize` tape facts (`FRXLog`, `FRXReadDefs`, `FRXReadLv`,
     `FRXChainFlock`, `FRXComputes`);
   - then re-check `decOk_decLN2`/`computes`.

   The Part 16 modules use no transcript constants.

---

## Part 17: revision 3.13 in the `FRX` modules; the fold's row step

**Revision 3.13.** The coordinator applied INT-2's patch to five modules (`FRXChainFlock`, `FRXLog`,
`FRXLogSpec`, `FRXLookup`, `FRXReadDefs`). I fixed the three modules still broken:
- `FRXReadLv`:
  - the cap offsets `capOffL` are now 19,584 / 35,968 / 44,160 / 52,352 / 60,544;
  - `capOffL_le` is now 60,544, and `capOffL_fit` ends at byte 64,640 (the final message's
    offset);
  - the control `capOffL_fsMsgs` is re-stated at the new FS positions 330, 369, 396 and 420
    (S-G's `capPos_eq`);
  - `π.size = 797,904`;
- `FRXLeaf`: `π.size = 797,904`;
- `FRXSeed`: `π.size = 797,904`, and the word bound `j < 99,738`.

No statement changed; only constants did. The Part 16 modules needed nothing, since their
positions are symbolic.

Two of 3.13's changes are not consumed yet:
- `E4end` (32 B) and `J_z = 4` enter only through `fsMsgs`/`chTab`, which are derived;
- the final message at 64,640 will be read by the level-4 message step (§3).

**The fold's row step** (`FRXFlag`, new: 249 / 196 code / 3 theorems). The module holds the
registers, the blocks `tPs` and `stepPs` with their lemmas, and **`fBody_sem`**. Take `W` at
`M[gW] = w` and the `eq` table entry at `M[gE] = e`. Then:
- `acc₀ += W·E.f₀` and `acc₁ += W·E.f₁` (`F`);
- `gW += 2`, `gE += 4`;
- the heap and the loop registers are kept.

The rest of `flagIR` is not written: the row loop, the comparison and store, and the position
loop.

**Checks.**
- Build (own tree `logs/fr-build-SH2`, on the worktree with INT-2's patch):
  `lake build FRXFlag FRXEncB FRXFwd FRXLevel FRXEqT FRXReadLv FRXBaryTop FRXExt FRXSpec FRXLeaf
  FRXAgree FRXComputes FRXSeed` is green, 2,287 jobs (`logs/S-H2/build17c.log`; the rebuild after
  3.13 is `build17a/b.log`).
- Axioms (`logs/S-H2/axioms17.log`):
  - these depend on `propext, Classical.choice, Quot.sound`: `computes`, `E_leaf`,
    `decOk_decLN2`, `readLv_spec_F`, `fBody_sem`, `level_decode`, `eqtIR_sem`, `fwdIR_enc`;
  - `capOffL_fsMsgs` depends on `propext`.
- Source rule: 117 files, 0 findings. No `sorry`.

**What remains** (Part 16 §7, unchanged in order):
1. `flagIR`:
   - the row loop: the `eqEnt_sem` loop pattern over `fBody_sem`;
   - the comparison: `eq`/`and` words, then `bW` of the two `F` equalities;
   - the store at `fb + j`;
   - the position loop: the `eqtIR_sem` pattern;
   - the conclusion against `mem_consSet_iff`.
2. The message rows (level 4: π's final field at 64,640).
3. The per-level composition, then level 0.
4. `decodeWit`'s output.
5. The `'N'` case.
6. The wiring.

**Stopped here.** The cause is context length.

---

## Part 18 (track S-H2i): `flagIR`, the message rows, one level's decode composed (levels 0–4)

**Delivered** (Part 17's list, items 1–4, each as "one level, with its inputs in memory"):
1. **`flagIR`** finished: the row loop, the comparison, the store at `fb + j`, the position loop;
   `flagV_consSet` states the flags against `mem_consSet_iff`.
2. **The message rows**: level 4 from π's final field at 64,640 (`msg4_next`), levels 0–3 from
   the next level's decoded rows (`msgH_next`).
3. **The per-level composition** `eqtIR ; msg ; fwdIR ×2 ; flagIR ; scanIR ; baryIR k R ;
   bflyIR ×R`, concluding with `level_decode` (`decLv_sem`), one theorem for all five levels.
4. **Level 0** (`decLv0_sem`: 64 rows, the word at `colBase`, `bary0`'s layout `lay0`).

**Not delivered** (§7): chaining the five levels with the reads, `decodeWit`'s output, the `'N'`
case, the wiring. `decSnark`, `ext`, `computes` and every earlier statement are unchanged; the
new modules are not on `ext`'s import path.

### 1. Files (code lines by the core's `scripts/loc.py`)

| File | total / code / theorems | What |
|---|---|---|
| `FRXFlag` | 855 / 717 / 23 (was 249 / 196 / 3) | `zPs`, `cmpPs`, `cmpPs2`, **`fEnt`**, **`flagIR n R cs cb eb xb yb fb`**; `WF`, `NoLoopT`, `outs`, `cost_flagIR`; `xor_eq_zero_w`, `wB_inj`, **`cmp_word`**; `zPs_sem`, `cmpPs_sem`, `cmpPs2_sem`, `TK`, **`fEnt_sem`**, `flagV`, **`flagIR_sem`**, **`flagV_consSet`**; control `toyFlag_run` |
| `FRXMsg` (new) | 984 / 837 / 37 | `zeroIR` (`zeroIR_sem`); `inW`, `finIn`, **`finIR`** (`finIR_sem`), `tapeF`; **`msgTIR`** (`msgTIR_sem`); `finOff`, `finW`, **`finPi`**, **`tapeF_fin`**; `gAd`, `gNx`, `gBody`, **`gathIR`** (`gathIR_sem`), `and7_toWord`; **`msgHIR`** (`msgHIR_sem`); **`msg4_next`**, **`msgH_next`**; costs |
| `FRXDecLv` (new) | 701 / 581 / 17 | `setA`, **`bfRowsIR`** (`bfRows_sem`); the memory map `fbF`, `obL`, `eqB`, `xbM`, `ybM`; **`decBackIR`** (`decBack_sem`); `MsgOk`, **`decFrontIR`** (`decFront_sem`); **`decLvIR`** (**`decLv_sem`**); `layLv`, `layLv0`, **`msgOk_four`**, **`msgOk_lower`**; `cbS`, `phStart_P1`, `cbS_le`, **`decLvU_sem`**, **`decLv0_sem`** |
| `FRXReadLv` | 183 / 108 / 17 | docstring table: the 3.13 cap offsets (no code change) |

New code in this part: 2,059 lines (521 + 837 + 581 + 0 + controls).

### 2. What is proved

**The flags** (`FRXFlag`). `fEnt` computes, for the position `j` in `gJ`, the two folds over the
`R` rows (`fBody`, the `eqEnt_sem` loop pattern), loads `Enc₀[j]`, `Enc₁[j]`, and stores
`gZ = [acc₀ = X[j] ∧ acc₁ = Y[j]]` at `fb + j`. `cmp_word` is the comparison:
`XOp.eq.eval ((a₀⊕e₀ | a₁⊕e₁) | (b₀⊕f₀ | b₁⊕f₁)) 0 = bW [⟨a₀,a₁⟩ = ⟨e₀,e₁⟩ ∧ ⟨b₀,b₁⟩ = ⟨f₀,f₁⟩]`.
`flagIR_sem`: with the rows of a position inside its stride (`2R ≤ cs`) and the inputs disjoint
from the flags,

```lean
(∀ j < n, rd (semXIR I (flagIR n R cs cb eb xb yb fb) s).M (fb + j) = flagV s.M R cs cb eb xb yb j) ∧
(∀ i, regs ≤ i → (i < fb ∨ fb + n ≤ i) → rd (semXIR I (flagIR …) s).M i = rd s.M i) ∧ Inv …
```

`flagV M R cs cb eb xb yb j` is `bW [Σ_{r<R} W[r][j]·E[r].f₀ = X[j] ∧ Σ_{r<R} W[r][j]·E[r].f₁ = Y[j]]`
on the heap. **`flagV_consSet`**: if `W` is `wordOf κ L es i`, `E` is `eqBits (sAt es i) ℓ`,
`X`, `Y` are `encF (mLog κ i)` of the next message's coordinates, then for `j < 2^logN`,
`j ∈ consN κ L es i ↔ flagV … j ≠ 0` (the `scanIR` input form of `firstK_scan`).

**The message rows** (`FRXMsg`). Both rows of `2^n` entries are zeroed (`zeroIR`), then:
- level 4 (`msgTIR 10 32 finW`): K element `x < 32` from tape words `finW + 4x … + 3`
  (`finW = 5 + 64,640/8`). `tapeF_fin`: those pairs are `finPi π x = chK (bytesAt π (64,640 + 32x) 32)`.
  **`msg4_next`**: with `hfin : ∀ x < 32, finalAt es x = finPi π x` (the chain link at C.4's absorb),
  `X[j] = if j < 2^mLog then (nextMsg .N30 L es 4 j).f₀ else 0`, and `Y` with `.f₁`, for `j < 2^10`;
- levels 0–3 (`msgHIR logN k obL`): `X[x]`, `Y[x]` are rows `2(x mod 8)` and `2(x mod 8) + 1` at
  column `x div 8` of the next level's decoded rows (`x & 7`, `x >> 3` on the machine).
  **`msgH_next`**: if the rows hold `msgOf (i+1)` as `F` values and `msgOf (i+1)` is `F`-valued,
  `X`, `Y` are the coordinates of `nextMsg i` (`nextMsg_coords`), zero-padded.

**One level** (`FRXDecLv`). `MsgOk I msg s n m g` is what a message step owes: from every state
agreeing with `s` outside the `eq` table, `msg` lays out `g` as above and keeps the heap outside
`[xbM, ybM + 2^19)`. `msgOk_four` and `msgOk_lower` discharge it for the two kinds of step.
**`decLv_sem`**: for `κ = N30`, `i < 5`, assume:
- the basis table at `tb0`, the word at `cb + cs·j + 2r` (`2^24 ≤ cb`), P1.i's challenges at `cbS`;
- `MsgOk` for `nextMsg i`;
- `¬ farL` and `A_c = jointAgree` (what `final` hands over);
- the level's `BaryLay` and the region bounds.

Then

```lean
∀ r < (lvl .N30 i).rows, ∀ x < 2 ^ mLog .N30 i,
  algebraMap F K (rdF (semXIR I (decLvIR msg i cs cb cbS ob) s).M (ob + 2 * 2 ^ mLog .N30 i * r + 2 * x)) =
    msgOf .N30 L es i r x
```

and the heap below `jb0`, in `[chB, eqB)` and from `2^24` on outside the rows is kept. The proof is
`decFront_sem` (the flags mark `consN`) then `decBack_sem` (`scanIR_sem`, `firstK_scan`,
`firstK_card` with `|A_c| ≥ k` from `decodeL_spec`, `baryIR_interp`, `bfRows_sem`,
`interpF_congr`, `level_decode`). `decLvU_sem` (levels 1–4: `cs = 32`, `cb = stB`, `ob = obL`) and
`decLv0_sem` (level 0: `cs = 128`, `cb = colBase`, `ob = ob0`) discharge the layout.

**The memory map** (words):

| region | base | size |
|---|---|---|
| basis table | `tb0 = 2^20` | 800 |
| `J` (scan list) | `jb0 = 2^21` | `k ≤ 2^17` |
| flags | `fbF = 2^21 + 2^18` | `n ≤ 2^18` |
| `DJ`, `W`, `E` | `djb0`, `wb0`, `eb0` | `2k` each |
| decoded rows, levels 1–4 | `obL = 2^22 + 2^21` | `2k·16 ≤ 2^19` |
| chain (answers at `ansB`) | `chB = 2^23 … chEnd` | read |
| `eq` table | `eqB = 2^23 + 2^15` | `4·2^ℓ ≤ 256` |
| `X`, `Y` | `xbM = 2^23 + 2^16`, `ybM = xbM + 2^19` | `2n` each |
| word of levels 1–4 / decoded rows of level 0 | `stB = ob0 = 2^24` | `2^21` / `2^24` |
| word of level 0 | `colBase = 2^25` | `2^25` |

Level `i + 1`'s rows at `obL` are read by level `i`'s gather before level `i`'s interpolation
overwrites them. Level 0's rows go to `ob0 = stB`, free once level 1's flags are computed.

### 3. Costs

Exact `cost_*` lemmas: `flagIR` `12 + n (92 + 156 R)`; `zeroIR` `14 + 9 n`; `finIR` `16 + 48 k`;
`gathIR` `16 + 560 k`; `msgTIR` `46 + 36·2^n + 48 k`; `msgHIR` `46 + 36·2^n + 560 k`;
`bfRowsIR` `1 + R (17 + m (741·2^(m−1) + 23))`.

Per level, `cost (decLvIR …) 0` evaluated in a scratch file outside the entry
(`logs/S-H2/axioms18.log`; the per-level `cost_decLvIR` lemmas are not written yet):

| level | 4 | 3 | 2 | 1 | 0 |
|---|---|---|---|---|---|
| steps | 14,546,064 | 261,035,116 | 13,186,204,712 | 823,525,089,508 | 140,024,626,811,056 |

- Sum of the five levels: 140,861,613,686,456 (`≈ 2^47.0`). The interpolations dominate.
- Add the four reads (4,843,569,208, `cost_readLv`), `decN` (`≤ 18,002·10^6 + 2,558 t`) and
  `wtabIR` (79,606): `≈ 140,884,459,335,270 + 2,558 t`.
- `decBudget t = 211,106,098,315,264 + 8,176 t` (`fuel_base` 211,106,232,532,992 less `2^27`;
  `fuel_per_word` 8,192 less 16). About `7.02·10^13 ≈ 2^46.0` is left for the output.
- Statements: `sizeIR` 7,882 (level 4) to 18,224 (level 0) per level.

### 4. Controls

| Control | Kind | Shows |
|---|---|---|
| `toyFlag_run` (`decide +kernel`) | positive / negative | a run of the compiled `flagIR` on a toy heap: position 0 agrees (`1·1 = X[0]`, `1·0 = Y[0]`) and is flagged `1`; position 1 does not (`X[1] = 0`) and is flagged `0` |
| `flagV_consSet`, `decLv_sem`, `decFront_sem`, `decBack_sem` | universal | for every log, transcript and level (`N30`) with the stated hypotheses; `not_farL_nil` (S-G) shows `¬ farL` is satisfiable |
| `msgOk_four`, `msgOk_lower` | inhabitants | `MsgOk` is met by the two message steps (it is not vacuous) |
| `layLv`, `layLv0`, `cbS_le` (`decide`) | value | the memory map meets `BaryLay` at every level; the challenges fit below `eqB` |
| `finOff_ctl` (`decide`) | value | the final message's offset follows level 4's cap (`capOffL 4 + 32·2^7`) and ends at the columns (68,736); `finW = 8,085` |

Missing: negative controls for `MsgOk`, `finPi` and the message programs (toy kernel runs of
`gathIR` and `finIR`).

### 5. Checks

- **Build**: `lake build FRXDecLv FRXMsg FRXFlag FRXEncB FRXFwd FRXLevel FRXEqT FRXReadLv
  FRXBaryTop FRXExt FRXSpec FRXLeaf FRXAgree FRXComputes FRXSeed` in `logs/fr-build-SH2i`
  (`logs/S-H2/build18.log`).
- **Axioms** (`logs/S-H2/axioms18.log`):
  - these depend on `propext, Classical.choice, Quot.sound`: `flagIR_sem`, `flagV_consSet`,
    `fEnt_sem`, `finIR_sem`, `gathIR_sem`, `msgTIR_sem`, `msgHIR_sem`, `tapeF_fin`, `msg4_next`,
    `msgH_next`, `bfRows_sem`, `decFront_sem`, `decBack_sem`, `decLv_sem`, `decLvU_sem`,
    `decLv0_sem`, `msgOk_four`, `msgOk_lower`;
  - `cmp_word`, `zeroIR_sem`, `toyFlag_run` depend on `propext, Quot.sound`; the cost lemmas and
    `layLv` on `propext`.
- **Source rule**: 123 files, 0 findings. No `sorry`.
- **Sequential profile** (`taskset -c 0`, `-DElab.async=false`;
  `logs/S-H2/FRX{Flag,Msg,DecLv}.{profile,time}`; the profiler printed no cumulative block, so
  type checking is the sum of the listed entries above 100 ms):

  | Module | wall | max RSS | type checking (listed) |
  |---|---|---|---|
  | `FRXFlag` | 44.8 s | 4.74 GB | 15.2 s (all of it `toyFlag_run`'s kernel run) |
  | `FRXMsg` | 71.2 s | 2.97 GB | 3.5 s |
  | `FRXDecLv` | 24.2 s | 2.88 GB | 1.8 s |

### 6. Deviations

1. **One level theorem for all five levels**, generic in the message step through `MsgOk`
   (a semantic interface the two message programs discharge), instead of five compositions.
2. **The level-4 link is a hypothesis**: `finalAt es x = finPi π x` (`x < 32`), the chain link at
   C.4's absorb, discharged in the `'N'` case as `capDig es i e = capPiL i π e` is.
3. **The gather is one loop** with `x & 7`, `x >> 3` per element, not a nested loop.
4. **The butterflies on the rows are unrolled** (`bfRowsIR`), so no loop register has to survive
   `bflyIR`.
5. **`κ = N30` is fixed** in the level theorems: the decoder runs on node proofs, whose ladder
   is `ladder30`.

### 7. What remains (in order; the next agent's list)

1. **A frame for the reads.** `readIR_sem` states the store and the index only. `posLoop` already
   carries the heap frame outside `[sb, sb + nw·np)`. A `readIR_frame` corollary (a new theorem,
   `readIR_sem` unchanged) is needed to keep the basis table, the chain's answers and level
   `i + 1`'s rows across `readLv i`.
2. **The five levels chained**, after `decN`:
   `wtabIR tb0 ; readLv 4 ; decLvIR (msgTIR 10 32 finW xbM ybM) 4 32 stB (cbS 4) obL ; readLv 3 ;
   decLvIR (msgHIR …) 3 … ; … ; decLvIR (msgHIR 18 (2^14) obL xbM ybM) 0 128 colBase (cbS 0) ob0`.
   The theorem threads:
   - `hT` from `wtabIR_sem`;
   - `hS` from `chain_dec` and `sAt_words` (with `fmAns … p = some (ansAt es p)`);
   - `hW` from `readLv_spec_F`/`read_spec_F` and `colL` ↔ `wordOf` through `capDig = capPiL`;
   - `msgOk_lower`'s `hdec` from the previous level's `decLvU_sem`, and `hF` from `msgOf_embed`;
   - the frames (`decLvU_sem`'s, the reads', `wtabIR_sem`'s).
3. **`cost_decLvIR`** per level, exact, from the component lemmas (`cost_baryIR` in general form if
   it is missing), and the sum within `decBudget` (§3's figures); `WF`, `NoLoopT`, `outs`, `size`
   of `decLvIR` (the components have them).
4. **`decodeWit`'s output** from `f⁽⁰⁾`'s rows at `ob0` (row `c` at `ob0 + 2^18 c`).
5. **The `'N'` case of `ext_good_tape`**: `vkOf π = vk`; `¬ farL`, `A_c = jointAgree` per level; the
   chain link (answers, `capDig = capPiL`, `finalAt = finPi`); `¬ StateHit L`.
6. **The wiring** into `decSnark`, re-checking `decOk`/`computes`.

**Stopped here.** The cause is context length. The state is commit-ready: the FRX targets build,
no `sorry`, the source rule is clean, and `ext`, `computes` and the earlier statements are unchanged.

## Part 19 (track S-H2j): the five levels chained, wired into `decSnark`; the node case up to the output

**Delivered** (Part 18 §7, items 1–3, 5 and 6; the task's A, B, C, E, F):
- **A.** `readIR_frame`: the ladder read keeps the heap outside its store (from `posLoop`).
  `readIR_sem` is unchanged.
- **B.** The five levels chained after the read (`decLevels`, **`decLevels_sem`**): level 0's
  decoded rows at `ob0` are `msgOf .N30 L es 0`, `F`-valued.
- **C.** Exact costs per level and in all (`cost_decLvIR`, `cost_levels`, `cost_decLevels`).
  `WF`, `NoLoopT`, `outs` and the size are proved for `decLvIR` and the chain.
- **E.** The node branch (`decNode_sem`), and the run of `ext` on a node proof (`ext_node`): it
  halts within the fuel, and its final heap holds `f⁽⁰⁾`. The chain links are hypotheses that
  `FinalLaw` supplies (§6, deviation 2).
- **F.** `decSnark := decLN3 = kindIR ; ite rKN decNode leafIR`, with `DecOk` and the cost
  `cost_le_decLN3` within 211,106,098,315,264 + 8,176·t.

**Not delivered: D** (`decodeWit`'s output on a node proof). It is blocked: no reader of the
packed witness exists yet (`FR.readSigned`, `reassemble` from `z`; A.5, A.7; S-E2's open item in
the `FRNodeCircuit` docstring). Until D lands, `ext` outputs nothing on a node proof, so
`E c π L = none` there (`ext_node`, first conjunct). About 2^46.0 steps are left for the output.

The statements of `decSnark`, `decOk_decSnark`, `ext`, `E`, `computes`, `ext_caps`, `E_W`,
`E_bad`, `E_leaf` and every earlier theorem are unchanged. `decSnark` is a `def`, and only its
body changed. `FRXLeaf`'s proof now names the new branch (`decNode`, `decLN3`).

### 1. Files (code lines by the core's `scripts/loc.py`)

| File | total / code / theorems | What |
|---|---|---|
| `FRXNode` (new) | 761 / 586 / 45 | `readIR_frame`, `readLv_frame`, `lvl_logN/sib/rows`, `p1_lt_nRep`, `readLv_wordOf`; `eqt_keep`, `lvMsg`, `msg4`, `msg4_keep`, `lvMsg_keep`; `stepU`, `KeepR`, **`lvStep_sem`**, `lv0Step_sem`; **`decLevels`**, **`decLevels_sem`**; `WF`/`NoLoopT`/`outs` of `setA`, `decLvIR`, `decLevels`; **`cost_decLvIR`**, `cost_msg4`, `cost_lvMsg`, **`cost_levels`**, **`cost_decLevels`**, `sizeIR_decLevels`; **`decNode`**, **`decLN3`**, `cost_decNode`, `outs_decNode`, **`decOk_decLN3`**, **`cost_le_decLN3`**; `chain_frame`, `wordOf0_eq`, **`decNode_sem`**; controls (`NodeControls`) |
| `FRXNodeRun` (new) | 121 / 94 / 1 | **`ext_node`** (the node case of `ext_good_tape`, up to the output) |
| `FRXExt` | +3 lines | imports `FRXNode`; `decSnark := decLN3`, `decOk_decSnark := decOk_decLN3` |
| `FRXLeaf` | 3 names in a proof | `decN`/`decLN2` → `decNode`/`decLN3` in `run_leaf`'s proof |

New code: 680 lines.

### 2. What is proved

**The program.**

```
decLevels := wtabIR tb0 ; stepU msg4 4 ; stepU (lvMsg 3) 3 ; stepU (lvMsg 2) 2 ; stepU (lvMsg 1) 1 ;
             decLvIR (lvMsg 0) 0 128 colBase (cbS 0) ob0
stepU msg i := readLv i ; decLvIR msg i 32 stB (cbS i) obL
msg4        := msgTIR 10 32 finW xbM ybM          lvMsg i := msgHIR (lvl .N30 i).logN (2^mLog (i+1)) obL xbM ybM
decNode     := decRead ; chainIR nRep chTab seedIR ; decLevels          decLN3 := kindIR ; ite rKN decNode leafIR
```

**The frames.**
- `readIR_frame`: every heap cell outside `[sb, sb + nw·np)` is kept.
- `readLv_frame`: for levels 1–4, the heap outside `[stB, stB + 32·2^logNL i)` is kept.
- `eqt_keep`: the heap outside `[eqB, eqB + 256)` is kept. It needs no hypothesis on the
  challenges.
- `chain_frame`: the heap outside `[chB, chEnd)` is kept (`chainIR_sem` for the seed block).

**One step** (`lvStep_sem`, `1 ≤ i ≤ 4`). The setting:
- `s₀` is the state after `wtabIR`. It holds the basis table, the chain's answers
  (`ansB + 4p + m`, `p < nRep`) and the sorted index.
- The current state `s` agrees with `s₀` on `KeepR`: below `jb0`, on `[chB, eqB)`, and from
  `2^25` on.
- The message step satisfies `MsgOk` from every state that agrees with `s` below `2^24` outside
  the `eq` table.

Given `capDig es i = capPiL i π`, `¬ farL` and `A_c = jointAgree` at level `i`, `stepU msg i`
leaves `msgOf i` at `obL`, keeps `KeepR`, and preserves `Inv`. On the way:
- `readLv_wordOf` turns `readLv_spec_F`'s `F` reading into `wordOf .N30 L es i`, through
  `(lvl .N30 i).sib = sibL i` and the cap link;
- `sAt_words` places P1.i's challenges at `cbS i`;
- `p1_lt_nRep` shows that the challenges' positions `phStart(26+5i) + 2v + 1` are below `nRep`.

`lv0Step_sem` is level 0's step, with the word at `colBase`.

**`decLevels_sem`** (hypotheses on the state before `wtabIR`):
- the sorted index at `memX`;
- level 0's word at `colBase` (`wordOf .N30 L es 0`);
- the answers `ansAt es p` at `ansB`;
- `capDig es i = capPiL i π` for `i ∈ [1,4]`, and `finalAt es x = finPi π x` for `x < 32`;
- `¬ farL` and `A_c = jointAgree` at every level.

Conclusion: `algebraMap F K (rdF M (ob0 + 2·2^17·r + 2x)) = msgOf .N30 L es 0 r x` for `r < 64`,
`x < 2^17`. Levels 3, 2, 1 and 0 get their message from the previous level's rows through
`msgOf_embed`, which supplies `F`-valuedness, and `lvMsg_keep`.

**`decNode_sem`** adds three hypotheses: the domain, `¬ StateHit L`, and the chain link
`fmAns (fsQ (vkOf π) c π) st₀ L p = some (ansAt es p)` (`p < nRep`); level 0's cap link
`capDig es 0 = capPi π` comes in with them. Then:
- `idxIR_sorted` and `read_spec_F` give the index and the word;
- `readIR_sem` keeps the index across `read0`;
- `chain_dec` gives the answers, and `chain_frame` keeps the index and the word;
- `decLevels_sem` finishes.

**`ext_node`** (`kindOf π = .snark .N30`, with the same hypotheses):
- `ext.run (extractorInput c π L) (fuel _) = some []`;
- the final state of `extIRWith decSnark` from `initSt (memX + 3t)` holds `f⁽⁰⁾` at `ob0`.

The proof follows `run_leaf`: the parse flags, `kindIR_regs` with the byte `0x4E`, `run_toProg`,
and `outs_le` with `outs decNode = 0`.

### 3. Costs (exact theorems), against the budget

| part | steps | theorem |
|---|---|---|
| level 4 | 14,546,064 | `cost_levels` |
| level 3 | 261,035,116 | `cost_levels` |
| level 2 | 13,186,204,712 | `cost_levels` |
| level 1 | 823,525,089,508 | `cost_levels` |
| level 0 | 140,024,626,811,056 | `cost_levels` |
| reads 4…1 | 4,843,569,208 | `cost_readLv` |
| basis table | 79,606 | `cost_wtabIR` |
| **`decLevels`** | **140,866,457,335,279** (`≈ 2^47.00`) | `cost_decLevels` |
| `decN` (chain + index + read 0) | `≤ 18,002·10^6 + 2,558 t` | `cost_decN` |
| **`decLN3`** | `≤ 140,884,459,335,297 + 2,558 t` | `decOk_decLN3.cost` |
| budget (`decBudget`) | 211,106,098,315,264 + 8,176 t | `cost_le_decLN3` |

The margin is 70,221,638,979,967 + 5,618 t (`≈ 2^45.997`). It is room for the output (D).
Statements: `sizeIR decLevels = 53,515` (`decide +kernel`) and `sizeIR decLN3 ≤ 74,568 < 2^19`.

### 4. Controls (`FRXNode.NodeControls`)

| Control | Kind | Shows |
|---|---|---|
| `toyFin_run` (`decide +kernel`) | positive / negative | the compiled `finIR` on the tape `[0,0,7,8,9,10]`: from `tw = 2`, `X[0] = (7,8)`, `Y[0] = (9,10)`; from `tw = 1` the element is shifted (`[0,7,8,9]`): the read is at `tw` |
| `toyGath_run` (`decide +kernel`) | positive / negative | the compiled `gathIR` on 16 toy rows: `X[x]` is row `2x`, `Y[x]` row `2x+1` (`[1,2,3,4]`); row 1 goes to `Y[0]`, not to `X[1]` |
| `msgOk_empty_neg` | negative | the empty step is not `MsgOk` for a nonzero message over a zero row: `MsgOk` is not trivial |
| `finPi_toy` (`decide +kernel`) | positive / negative | a `1` at byte `finOff` makes `finPi π 0 ≠ 0`; a `1` at `finOff − 1` is not read |
| `keepR_ctl` | positive / negative | `KeepR` holds at `tb0`, `ansB`, `colBase` and fails at `obL`, `ob0` (the decode writes them) |
| `decLevels_sem`, `decNode_sem`, `ext_node` | universal | for every log, transcript and proof with the stated hypotheses; `msgOk_four`, `msgOk_lower` (Part 18) inhabit `MsgOk` |
| `toy_W`, `toy_W_exact`, `toy_bad` (FRXSpec, unchanged) | positive / negative | still kernel-checked with the new `decSnark` compiled in |

### 5. Checks

- **Build**: the whole entry, `lake build FR FRXNodeRun`, is green in `logs/fr-build-SH2j`
  (2,347 jobs; 3 min 4 s wall on the shared VM; `logs/S-H2/build19.{out,log}`). The tree is a
  snapshot: HEAD's modules of the other tracks (`snap.sh`; S-E8 is editing `FRVIR*` in the
  worktree), with `FRXNode`, `FRXNodeRun`, `FRXExt`, `FRXLeaf` symlinked to the worktree.
- **Axioms** (`logs/S-H2/axioms19.log`):
  - these depend on `propext, Classical.choice, Quot.sound`: `computes`, `ext_caps`,
    `decOk_decSnark`, `decOk_decLN3`, `cost_le_decLN3`, `cost_decLevels`, `cost_levels`,
    `cost_decLvIR`, `ext_node`, `decNode_sem`, `decLevels_sem`, `lvStep_sem`, `lv0Step_sem`,
    `readIR_frame`, `readLv_frame`, `readLv_wordOf`, `chain_frame`, `ext_W`, `ext_bad`, `E_leaf`,
    `ext_encode`, `msgOk_empty_neg`, `keepR_ctl`;
  - `toyFin_run`, `toyGath_run` and `finPi_toy` depend on `propext, Quot.sound`;
    `sizeIR_decLevels` depends on `propext`.
- **Source rule**: 128 files, 0 findings (`logs/S-H2/source19.log`). There is no `sorry`.
- **Sequential profile** (`taskset -c 0`, `-DElab.async=false`, `logs/S-H2/*.19.{profile,time}`):

  | Module | wall | max RSS | type checking (listed entries) |
  |---|---|---|---|
  | `FRXNode` | 70.4 s | 5.49 GB | ≈ 49 s, almost all of it the toy kernel runs: 23.3 s (`finPi_toy`, a 64,641-byte toy proof), 20.5 s and 4.5 s (`toyGath_run`, `toyFin_run`); `sizeIR_decLevels` 0.9 s |
  | `FRXNodeRun` | 7.6 s | 2.75 GB | below 100 ms |
  | `FRXSpec` | 12.4 s | 2.85 GB | 0.43 s (the toy runs, with the new `decSnark` compiled in) |
  | `FRXLeaf` | 9.3 s | 2.76 GB | below 100 ms |
  | `FRXExt` | 5.9 s | 2.73 GB | below 100 ms |

### 6. Deviations

1. **Program order: the chain after the read.** `decNode := decRead ; chainIR ; decLevels`;
   `decN` (chain first) is kept but is no longer on `ext`'s path. `chainIR_sem` has a heap frame
   (outside `[chB, chEnd)`), and the index (`idxIR`: walk and merge sort) has none. With the chain
   last, its frame keeps the index at `memX` and level 0's word at `colBase`, and no frame of the
   sort is needed. The cost is the same (`cost_decNode = cost decN + cost decLevels + 1`).
2. **E: the chain links are hypotheses of the `'N'` case, which `FinalLaw` supplies.** The links
   are:
   - `fmAns (fsQ (vkOf π) c π) st₀ L p = some (ansAt es p)` for `p < nRep`;
   - `capDig es i = capPiL i π` (and `capPi π` at level 0);
   - `finalAt es x = finPi π x` for `x < 32`;
   - `¬ StateHit L`;
   - `¬ farL` and `A_c = jointAgree` per level.

   They are hypotheses because each one relates the transcript `es` to `L` and to π, and `es` is
   free on the extractor's side. It is the transcript the verifier's run reads off `L`. These
   facts come from `(V vk c π).runLog L = some true`: `runLog_chain` says the queries are `fsQ`'s
   and the answers are the first-match chain, and the absorbed caps and final message are π's
   fields. That is `final`'s side (S-G2/S-G3). The `FRX` modules do not import the verifier's
   semantics, and they should not: the program does not depend on them. `ext_good_tape`'s `'N'`
   case is used inside `FinalLaw`'s proof, where `runLog = some true` is available.

   A reduction is possible. If `es`'s queries are `fsQ`'s, then `capOffL_fsMsgs` (and its level-0
   and final-message twins) turn the cap and final links into consequences of that one fact,
   because `msgAt es (capPos i)` is π's bytes at `capOffL i`. That needs a lemma
   `msgAt (fsQ …) = π.extract …`, which is not written (§8).
3. **The seed state `st₀` is a parameter** (as in `chain_dec`); `final` instantiates it with the
   verifier's seed.
4. **D is not delivered** (blocked, above). `ext_node` states what the output step will
   consume: `f⁽⁰⁾` at `ob0`.
5. **`FR.lean` does not import `FRXNodeRun`.** `FR.lean` is not an `FRX` module, so I did not
   edit it. `FRXNode` is imported through `FRXExt`. The orchestrator should add
   `import FRXNodeRun` to `FR.lean`. It builds (`lake build FRXNodeRun` above).

### 7. Pitfalls (also in the journal)

- **`omega` and large atoms.** `omega` fails with "maximum recursion depth" when an atom is a
  large closed term (`sizeIR decRead`, `(semXIR I (wtabIR tb0) s).M.size`). It appears to compare
  atoms up to definitional equality. Fix: `generalize` the atoms first, or give constant bounds by
  `le_trans (by decide) …` (`le_add3`, `le_add4`). This is probably Part 18's pitfall too.
- **A fact stated with an unfolded definition.** `readIR_sem` gives a fact about
  `semXIR … (readIR 0 capW0 …) s1`, while the goal has `read0`. `generalize` did not abstract
  it, and a later `.trans` made the elaborator evaluate `semXIR` (a whnf timeout reported at the
  declaration). Fix: state the fact with the folded name.

### 8. What remains (in order)

1. **D, the output** (BLUEPRINT §6.2 step 5, §6.5 `output_spec`). It needs:
   - a reader `z ↦ (c₁, c₂, p₁, p₂)` of the packed witness `z := unpack f⁽⁰⁾`
     (`FR.readSigned σ z`, `reassemble` of A.5, the A.7 cell map; S-E2/L-circ);
   - then an output program from the rows at `ob0` (row `c` at `ob0 + 2^18 c`), proved to emit
     `witWords (.node c₁ c₂ p₁ p₂)`, so that `decodeWit_witWords` gives `E c π L = some w`;
   - a cost within the ≈ 7.0·10^13 margin (§3).
2. **The links on `final`'s side**: discharge `ext_node`'s transcript hypotheses from
   `runLog = some true` (S-G2/S-G3). Optionally, reduce the cap and final links to "the queries
   are `fsQ`'s" (§6, deviation 2).
3. `import FRXNodeRun` in `FR.lean` (orchestrator).
4. Kernel time of the new controls (≈ 49 s): `finPi_toy` could use a congruence lemma instead
   of a 64 kB toy proof, if the 600 s kernel budget gets tight.

## Part 20 (track S-H2k): `FR.readSigned`, `reassemble` field by field, the trace and signature in words; the toys' kernel cost

**Delivered:** item 1 (`FR.readSigned`, with controls), item 4 (the toys' kernel cost), and the
pure half of item 2: `reassemble` field by field, and the trace and the signature as word lists.

**Not delivered: the output program (item 2's machine half) and `ext_node`'s output (item 3).**
§5 gives the plan in order. The statements of `ext`, `E`, `computes`, `ext_caps`, `decSnark` and
`ext_node` are unchanged. Until the output program lands, `E c π L = none` on a node proof.

### 1. Files (code lines by the core's `scripts/loc.py`)

| File | total / code / theorems | What |
|---|---|---|
| `FRNodeRead` (new) | 231 / 119 / 12 | `streamCell`, `streamWord`, `streamWords`, `stream`, `entryAt`, `readItems`, `readTrace`, `digestW`, `digestOf`, `lCell`, `readSig`, `readStmt`, **`FR.readSigned`**, **`FR.readWit`**; `readTrace_length`, `stream_length`, `entryAt_of`, **`readItems_traceBytes`**, **`readTrace_of_stream`**, `stream_getD`; controls |
| `FRNodeReadW` (new) | 362 / 273 / 23 | `ctb`, `ansOf`, `ctbs`, `cont`, `Appends`, `foldl_appends`, `rsPhase_spec`, `foldl_rsPhase`, **`reassemble_eq`**; `readTrace_getD`, **`qBytes_readTrace`**; `wordsBytes_drop`/`_take`, `stream_slice`; `entryW`, `trW`, `entryW_aligned`, `readItems_words`, **`logWords_readTrace`**; `packBytes_digestOf`, **`sigWords_readSig`** |
| `FRNodeReadLayout` (new) | 31 / 11 / 3 | `consts_eq`, **`streamCell_seedCell`**, `readStmt_cells` (against `FRNodeLayout`/`FRNodeCircuit`) |
| `FRXNode` | 790 / 614 / 46 (+41 −12 lines) | `toyGath_run` → `toyGath_ctl`; `finPi_toy` re-proved (`byteAt_toyPi`) |

New code: 403 lines. `FR.lean` should import **`FRNodeRead`, `FRNodeReadW`, `FRNodeReadLayout`**,
and `FRXNodeRun` (Part 19).

### 2. What is defined and proved

**The reader (`FRNodeRead`).** `w : ℕ → F` is the committed witness in A.7's element view:
`w e = f[e]`, `z = unpack f⁽⁰⁾`, `f⁽⁰⁾ = pack z`. On the extractor's side,
`w e = (msgOf .N30 L es 0 (e % 64) (e / 64)).f₀`, which is S-G's `fF .N30 L es e`. Slots are
`σ ∈ {1, 2}`.
- `streamCell σ e := ((σ−1)·chainLen + ⌊e/4⌋)·128 + 4 + e mod 4`. This is A.7's map, and
  `FRBlockStream.elem_slot`'s: stream element `e` is message slot `4 + e mod 4` of block `⌊e/4⌋`.
- `streamWord w σ u` is coefficient `c_{u mod 2}` of element `⌊u/2⌋`. `stream w σ` is the
  `streamBytes = 1,481,344` bytes of the 185,168 words (`wordsBytes`, little-endian, as A.7's
  byte order).
- **`readTrace w σ`** reads the item sequence's shape: item `k` sits at `streamOff k` with
  `|q| = items[k].qlen`. The length word `enc64 |q|` is **not** read: the circuit asserts it
  (§4.3 (2)).
- `readSig`: `idx` is `c₀` of element 0 of slot `σ`'s L region (`lBase·128 + (σ−1)·2^14`), then
  the 133 chain values and the 16 path digests, two elements each (`digestOf`: bytes 0–15, then
  16–31, as `Node.halves`).
- `readStmt` is stream elements 3–4, the seed payload's `c` (`PubCells`' `cᵢ`,
  `readStmt_cells`).
- **`FR.readSigned σ w := ⟨reassemble (readTrace w σ), readTrace w σ, readSig w σ⟩`**;
  **`FR.readWit w := .node (readStmt w 1) (readStmt w 2) (readSigned 1 w) (readSigned 2 w)`**.

**`reassemble` field by field (`reassemble_eq`).**

```
bl (reassemble tr) = (range 18).flatMap (ctbs (traceKind tr.toArray) tr.toArray 0 [] (phases.map shape))
```

Here `ctb k a ix ans sh f` is phase `sh`'s contribution to field `f`: the `qBytes` slices of its
items from item `ix`, and for `queries i` and field 17 the `sibling` halves with
`posOf k i ans p`. `ctbs` threads `ix` (`+ sh.items.length`) and `ans` (`ansOf`: a `P2` phase's
answers) through the phases. The proof goes through the walk's state field by field: `cont`,
`cont_put`, `Appends`/`foldl_appends`, `rsPhase_spec` per shape, `foldl_rsPhase`.

**The trace on the stream.**
- `readTrace_getD`: entry `j` is `entryAt (stream w σ) (streamOff j) items[j]`.
- **`qBytes_readTrace`**: query bytes `[off, off + n)` of item `j` are stream bytes
  `[streamOff j + 8 + off, +n)`.
- `stream_slice`: an aligned stream slice is `wordsBytes` of a word slice.
- **`logWords_readTrace`**:
  `logWords (readTrace w σ) = toWord 8891 :: entryW (seed entry at offset 1) ++ trW W 20 items.tail`,
  where `trW` is, per later item, `toWord qlen` followed by the next `qlen/8 + 4` stream words.

**The signature (`sigWords_readSig`).** `toWord idx`, then `elemWords` of the two L cells of
each chain value and each path digest, in order.

### 3. Controls

| Control | Kind | Shows |
|---|---|---|
| `readItems_traceBytes`, **`readTrace_of_stream`** | positive (universal) | on `0x54 ‖ traceBytes tr` with `tr` of the item shape, `readTrace = tr`: the reader inverts the hashed stream (`stream_traceDigest`'s bytes) |
| `readSig_idx_ctl` | positive / negative | `idx = 5` from `c₀ = 5`; `c₁ = 5` gives `idx = 0`; slot 2 does not read slot 1's cell |
| `readStmt_ctl` | positive / negative | byte 0 of `c₁` is element 3's low byte; a change in element 2 (`vk`'s high half) does not change it |
| `streamCell_seedCell`, `consts_eq`, `readStmt_cells` | link | the cells are `Node.seedCell`'s, and the constants are `Layout.lBase`, `Layout.chainN` |
| `reassemble_eq` | universal | for every trace |
| `toyGath_ctl` (replaces `toyGath_run`) | positive / negative | `gathIR`: `X[0]`, `Y[0]`, `X[1]` are rows 0, 1, 2; `X[1]` is not row 1 when rows 1 and 2 differ (from `gathIR_sem` on every state) |
| `finPi_toy` (same statement) | positive / negative | as before; the proof reduces the toy to its 32 read bytes (`byteAt_toyPi`) |

### 4. Checks

- **Build**: `lake build FR FRXNodeRun FRNodeRead FRNodeReadW FRNodeReadLayout` is green in
  `logs/fr-build-SH2k` (2,350 jobs; 3 min 54 s wall on the shared VM;
  `logs/S-H2/build20.{out,log}`). The tree is a HEAD snapshot (`snap.sh`); my modules are
  symlinks.
- **Axioms** (`logs/S-H2/axioms20.log`):
  - these depend on `propext, Classical.choice, Quot.sound`: `computes`, `ext_caps`,
    `ext_node`, `decNode_sem`, `cost_le_decLN3`, `toyGath_ctl`, `finPi_toy`, `reassemble_eq`,
    `readTrace_of_stream`, `readItems_traceBytes`, `readStmt_ctl`, `readTrace_getD`,
    `qBytes_readTrace`, `logWords_readTrace`, `sigWords_readSig`, `stream_getD`;
  - `toyFin_run` and `readSig_idx_ctl` depend on `propext, Quot.sound`;
  - `streamCell_seedCell`, `readStmt_cells` and `consts_eq` depend on `propext`.
- **Source rule**: 136 files (the worktree, other tracks' new files included), 0 findings
  (`logs/S-H2/source20.log`).
- **Sequential profile** (`taskset -c 0`, `-DElab.async=false`, `logs/S-H2/*.20.{profile,time}`):

  | Module | wall | max RSS | type checking |
  |---|---|---|---|
  | `FRXNode` | **26.6 s** (was 70.4 s) | 3.35 GB | 4.45 s `toyFin_run` (unchanged), 0.84 s `sizeIR_decLevels`; the rest below 0.2 s |
  | `FRNodeRead` | 12.2 s | 2.86 GB | 2.3 s and 2.4 s (the concrete controls) |
  | `FRNodeReadW` | 14.9 s | 3.02 GB | 3.5 s (`decide +kernel` over the item sequence's lengths in `logWords_readTrace`) |
  | `FRNodeReadLayout` | 5.8 s | 2.71 GB | below 0.1 s |

- **Kernel cost of the toys (item 4), measured.** A concrete kernel run of the DSL costs
  ≈ 185 ms per machine operation on a 296-cell memory: `decide +kernel` of 20 `add`s takes
  3.7 s, with `semXIR` as with `toProg`. `toyGath` through `semXIR` takes 20.3 s, and one
  iteration of `gBody` 5.7 s. No run of `gathIR` (8k iterations) fits 3 s, so its control is
  stated from `gathIR_sem`. `finPi_toy` went from 23.3 s to 0.2 s with the same statement.
  `toyFin_run` (4.5 s) was not in the brief and is unchanged.

### 5. What remains (in order): the output program and `ext_node`

1. **The words of the proof** (pure, `FRNodeReadW`). Per shape, `ctb` on
   `(readTrace w σ).toArray` at the phase's start `ix` is `wordsBytes` of stream word slices.
   - Use `qBytes_readTrace` and `stream_slice`.
   - Add the arithmetic of `streamOff` inside a phase:
     `streamOff (ix + j) = streamOff ix + Σ_{<j} slen` over `sh.items`. Rounds have stride
     `slen(abs) + 80`, queries `slen(col) + 80·sib`.
   - Every slice is aligned: offsets `o + 48` (absorb, uni, rounds), `o + 16` (columns),
     `o + 48` or `o + 16` (siblings), `80…127` (`hdr`, words 10–15). Every length is a multiple
     of 8.
   - The sibling is `bl (sibling …) = wordsBytes` of 4 words or `[0,0,0,0]`. Its bit is
     `posOf k i ans p / 2^h % 2 = bit (idx·logN + h) of natLE(answer)`, with
     `idx = p mod per` and answer `p / per` of the preceding `P2` phase. That is bit
     `m mod 64` of answer word `⌊m/64⌋`, and the answer's words are stream words
     (`entryAt`'s answer is `digestW` of 4 stream words).
   - The kind: `traceKind` is the low byte of stream word 10.
   - Also needed: `(reassemble (readTrace w σ)).size = piSize` (for `bytesWords`), the seed
     entry's 15 shifted query words (`(W[1+i] >>> 8) ||| (W[2+i] <<< 56)`, the last `W[15] >>> 8`),
     and `Wit.Fits (readWit w)` for `decodeWit_witWords`.
2. **The output program** (`FRXOut`, after `decLevels`; only `f⁽⁰⁾` at `ob0` is live then).
   - Gather each slot's 185,168 stream words into a free region, for example `obL`
     (`[obL, obL + 185,168) ⊂ [obL, chB)`). Word `u` of slot `σ` is at
     `ob0 + 2^18·(4 + (u/2) mod 4) + 4·((σ−1)·23,146 + ⌊u/8⌋) + u mod 2`, from
     `f[g] = rdF (ob0 + 2^18 (g mod 64) + 2 ⌊g/64⌋)`.
   - Then emit `1`, `c₁`, `c₂`, and per slot `piSize`, the proof's words field by field
     (`reassemble_eq`), `logWords` (`logWords_readTrace`), and the signature
     (`sigWords_readSig`, from L at `f`'s rows 0–63).
   - A segment language keeps the program small and the proofs generic: constant word; copy
     `n` words; repeat `c` times with stride `s` over a body of leaves; the sibling leaf
     computes its bit from the repetition counter `p` and per-kind registers (`logN`, `per`,
     `sib`).
   - The output is ≈ 571,000 words (`< outCap = 2^24`) and needs ≈ 10^7 steps, against the
     ≈ 7.0·10^13 margin of Part 19 §3.
3. **`ext_node`**: `decNode := decRead ; chainIR ; decLevels ; outIR` (the body only), with
   `E c π L = some (readWit (fun e => (msgOf .N30 L es 0 (e % 64) (e / 64)).f₀))`. Keep
   Part 19's chain-link hypotheses as they are.

### 6. Deviations and choices

1. **The element view.** `readSigned σ w` takes `w : ℕ → F` (`f⁽⁰⁾`), not the bit vector `z`.
   The blueprint's `FR.readSigned σ z` is `readSigned σ (pack z)`, and on the extractor's side
   `z = unpack f⁽⁰⁾` (`pack_unpack`). The circuit's cells (`PubCells`, `SlotHolds`) are
   element-valued too.
2. **The trace's shape is fixed; the length word is not read.** A data-dependent parse would
   make the output's offsets data-dependent. With the circuit's length asserts,
   `readTrace_of_stream` gives back the hashed trace.
3. **`idx` is `c₀`** of the first `sig` element. A.7 says "idx 1 element" without an encoding.
   The `j` mirror source is 16 bytes, zero-padded (A.6), which matches `c₀ = j`, `c₁ = 0`.
4. **The L base is `FRNodeLayout.lBase = 47,616`.** A.7 and the §4.3 table still say 46,336
   (revision 3.12 moved L; `FRNodeLayout`'s docstring). This needs a blueprint fix.
5. **`toyGath_run` is replaced by `toyGath_ctl`**, a statement from the semantic lemma, because
   a concrete run cannot meet 3 s (§4).

### 7. Pitfalls (also in the journal)

- `norm_num` or `omega` on a goal that contains `semXIR … (gathIR …)` or `streamBytes`
  evaluates them (whnf timeout, max recursion). `generalize` the state, or rewrite with
  `streamBytes_eq` first.
- `rfl`/`congr 1` on goals with `items`/`readTrace` recurses; use `refine congrArg …` and
  `decide +kernel` for closed facts about the item sequence.
- `simp only [List.foldl_map] at …` followed by `generalize` made the kernel unfold the phase
  walk (32 s, deep recursion). Stating the folded form first (`have e : reassemble tr = …
  := by rw [List.foldl_map]; rfl`) costs nothing.

## Part 21 (track S-H2l): the node output (`FRXOut`), `E c π L = some (FR.readWit …)`

**Delivered:** Part 20 §5 items 1–3.
- **Item 1 (pure).** Per-phase word slices of `ctb` (`pPh`, `pRest`, `pSeg`) with the
  within-phase `streamOff` arithmetic (`drop_rep`, `drop_cons_item`), the sibling bit from the
  answer words (`ans_bit`, `testBit_posOf`, `sib_one`), `(reassemble …).size = piSize`
  (`reassemble_size`), the seed entry's 15 shifted words (`entryW_seed`), and
  `Wit.Fits (readWit w)` (`readWit_fits`).
- **Item 2 (the program).** `outIR` (`FRXOutRun`), compiled from a segment language (`Seg`,
  `FRNodeReadS`; `segIR`, `FRXOut`). Its semantics (`outIR_out`), exact cost, `WF`, `NoLoopT`,
  `outs` and size are proved.
- **Item 3.** `decNode := decF0 ; outIR`, with `decF0` the old body
  (`decRead ; chainIR ; decLevels`). Then `ext_node` gives
  `ext.run … = some (witWords (FR.readWit w))`, and `E_node` gives
  `E c π L = some (FR.readWit w)`. Here `w e = (msgOf .N30 L es 0 (e % 64) (e / 64)).f₀`, which
  is `fF .N30 L es e` by unfolding `fTab`.

`ext`, `E`, `computes`, `ext_caps`, `decSnark`, `cost_le_decLN3` and `decNode_sem` keep their
statements. Only `decNode`'s body, `cost_decNode`, `outs_decNode` and `ext_node`'s first
conjunct changed. Part 19's chain-link hypotheses are unchanged.

### 1. Files (code lines by the core's `scripts/loc.py`)

| File | total / code / theorems | What |
|---|---|---|
| `FRNodeReadS` (new) | 478 / 352 / 31 | `Seg`, `segOut`, `segLen`, `sibW`; the trace: `trWf`, `tItems`, `tPh`, `tSegs`, `trSeg`, **`logWords_trSeg`**; the seed: `seedSeg`, `shw_bytes`, `sh8_bytes`, **`entryW_seed`**; the signature: `lWord`, `sigSeg`, **`sigWords_sigSeg`**; **`stmtWords`** |
| `FRNodeReadP` (new) | 684 / 516 / 49 | `wo`, `pPh`, `pRest`, **`pSeg`**, `kflag`, `kOf`, `PrevInv`, `qOk`; `streamOff_drop`, `drop_rep`, `qB`, `cpSlice`, `ans_bit`, `sib_one`, `pPh_spec`, `pRest_spec`; **`traceKind_lvl`**, **`proof_words`**, `segLen_pSeg`, **`reassemble_size`**, `slotSeg`, **`signedWords_readSigned`**, **`witWords_readWit`**, **`readWit_fits`**; controls (`ReadControls`) |
| `FRXOut` (new) | 1,015 / 868 / 49 | registers, `AP`, `addrW`, `src`, `ldw`, `cpIR`, `sibHit`/`sibH`/`sibP`/`sibIR`, **`segIR`**, `depthSeg`, `okSeg`, `Ctx`, `Prot`; `wrL`, `ow_segIR`, `noW_segIR`, `wf_segIR`, `loK_segIR`, `noLoopT_segIR`, `ctx_segIR`; `iterL_emit`, `loopK_emit`, `ldw_sem`, `cpIR_sem`, `sibHit_sem`, `sibH_sem`, `sibP_sem`, `sibIR_sem`, **`segIR_sem`** |
| `FRXOutRun` (new) | 382 / 277 / 31 | `apS`, `apL`, `baseS`, `baseL`, `kflagIR`, `slotIR`, **`outIR`**; `cost_outIR`, `outs_outIR`, `sizeIR_outIR`, `wf_outIR`, `noLoopT_outIR`; `addrS_toNat`, `addrL_toNat`, `src_stream`, `src_l`; `seg_step`, `kflag_step`, `setR_step`, `sig_step`, `slot_step`, **`outIR_out`**; controls (`OutControls`) |
| `FRXNode` | 876 / 683 / 52 (+69 code) | `decF0` (the old body), `decNode := decF0 ; outIR`, `cost_decF0`, `cost_decNode`, `outs_decF0`, `outs_decNode`, `decOk_decLN3` (updated), **`cost_le_decLN3_node`**, `decF0_sem` (the old `decNode_sem`), `loK_outIR`, **`decNode_sem`** (same statement), **`decNode_out`** |
| `FRXNodeRun` | 142 / 112 / 2 (+18 code) | **`ext_node`** (first conjunct: the witness), **`E_node`** |
| `FRXExt` | docstring | `decSnark`'s docstring |
| `FRNodeReadW` | +2 lines | `tail_slen_le` (the 3.5 s `decide +kernel` of `logWords_readTrace`, shared) |

New code: 2,013 lines (four new modules), plus 87 lines in `FRXNode` and `FRXNodeRun`.

### 2. What is proved

**The segment language (`FRNodeReadS.Seg`).**
- A segment denotes words over a word source `W : ℕ → Word`, from a base `b`
  (`segOut W κ b`). The constructors are `wd x`, `cp o n` (the words `W (b + o + j)`),
  `rep c s x` (`x` at bases `b + s j`), `cat`, `shw`/`sh8` (the seed's straddling words),
  `kite` (by the child's kind flag `κ`) and `sib` (`sibW`: one level's siblings).
- Every word of the witness is a constant, a stream word, an L word, a shifted pair of stream
  words, or a sibling chosen by a stream-word bit. The proofs are therefore generic in the
  phase table: one induction over the phases, with a step lemma per shape.

**The child's words, pure (`FRNodeReadP`, `FRNodeReadS`).** Here `W` agrees with
`streamWord w σ` below 185,168, and `WL` with `lWord w σ` below 598.
- `logWords (readTrace w σ) = segOut W κ 0 trSeg`. The count, the seed entry (`entryW_seed`),
  then per phase a `rep` over its items. The length words are constants `toWord qlen`, as ruled.
- `bl (reassemble (readTrace w σ)) = wordsBytes (segOut W (kflag (W 10)) 0 pSeg)`
  (`proof_words`). This rests on `reassemble_eq`, then `pRest_spec`, an induction over
  `restSh` with `PrevInv` and the decided `qOk`.
  - `absorb`, `uni` and the rounds' messages start 6 words after their item. Round `j` sits
    `j·wsum[absorb, squeeze]` words on.
  - Columns start 2 words after the column item, with positions `wsum (posItems i)` apart.
  - A sibling is node words 6–9 (bit 0) or 2–5 (bit 1), or four zero words at a dummy depth.
    Its bit is bit `m mod 64` of answer word `⌊m/64⌋`, with `m = (p mod per)·logN + h`.
- The child's kind flag is `kflag (W 10)`. `traceKind_lvl` shows that the trace's kind and
  the flag's ladder agree on every level (byte 80 of the stream is word 10's low byte).
  `P30` and `N30` share `ladder30`.
- `segLen κ pSeg = 99,738` (`decide +kernel`), so `|reassemble| = 797,904 = piSize`
  (`reassemble_size`).
- `sigWords (readSig w σ) = segOut WL _ 0 sigSeg` (`idx`, then L elements 1–298).
  `packBytes (readStmt w σ)` is stream words 6–9.
- These assemble into `witWords_readWit`: the tag, both statements, then per slot `slotSeg`
  over the stream and `sigSeg` over L. Also `readWit_fits`.

**The program (`FRXOut`, `FRXOutRun`).**
- `outIR` does no store. Each source word is one computed load,
  `addrW ap R n = R + (((n>>1) & m₁) << 18) + ((n >> s₃) << s₄) + (n & 1)`:
  - a stream word (`apS = (3, 3, 2)`, `R = baseS σ = ob0 + 2^20 + 4·(σ−1)·23,146`) is
    `streamWord w σ u` (`src_stream`);
  - an L word (`apL = (63, 7, 1)`, `R = baseL σ = ob0 + 2·(2·47,616 + (σ−1)·256)`) is
    `lWord w σ v` (`src_l`).

  So neither slot needs a gather. `obL` is not used.
- `segIR_sem`: in context (`Ctx`: the heap is `M₀`'s, `rR = R`, the flag), `segIR ap d seg`
  appends `segOut (src M₀ ap R) κ b seg`. The loops use one lemma, `loopK_emit`, with an
  invariant `Q`. The sibling loop keeps `p mod per`, `(p mod per)·logN` and the answer pointer
  in registers (`succ_divmod`).
- **`outIR_out`**: if the heap holds `w` at `ob0`, that is
  `rdF M (2^24 + 2^18 (e mod 64) + 2⌊e/64⌋) = w e` for `e < 2^23`, then `outIR` appends
  `witWords (FR.readWit w)`.
- **Exact numbers:**
  - `cost outIR t = 21,609,039`;
  - `outs outIR t = 571,019` (`= |witWords|`, `≤ outCap = 2^24`);
  - `sizeIR outIR = 22,421`.

  The numbers were read off a scratch `#eval` outside the entry and then proved by
  `decide +kernel`, with `cost_noLoopT` and `outs_noLoopT`.

**The node branch.**
- `decNode_out`, under `decNode_sem`'s hypotheses: `decNode`'s output is `decF0`'s, then
  `witWords (FR.readWit w)`.
- `ext_node`: `ext.run (extractorInput c π L) (fuel _) = some (witWords (FR.readWit w))`, and
  the heap still holds `f⁽⁰⁾`.
- **`E_node`**: `E c π L = some (FR.readWit w)` (`decodeWit_witWords` with `readWit_fits`).

### 3. Costs, against the budget

| part | steps | theorem |
|---|---|---|
| `outIR` | 21,609,039 | `cost_outIR` |
| `decNode` | `cost decN + 140,866,457,335,279 + 21,609,041` | `cost_decNode` |
| **`decLN3`** | `≤ 140,884,480,944,337 + 2,558 t` | `cost_le_decLN3_node` |
| budget | 211,106,098,315,264 + 8,176 t | `cost_le_decLN3` (statement unchanged) |

The margin is now 70,221,617,370,927 + 5,618 t. Sizes: `sizeIR outIR = 22,421`, and
`sizeIR decLN3 ≤ 96,990 < 2^19` (`decOk_decLN3.size`).

### 4. Controls

| Control | Kind | Shows |
|---|---|---|
| `logWords_trSeg`, `proof_words`, `sigWords_sigSeg`, `stmtWords`, `witWords_readWit` | positive (universal) | for every `w` and every word source agreeing with it, the segments denote exactly the contract's words |
| `segOut_cp_ctl` (`decide`) | positive / negative | `cp 6 4` starts at word 6; `cp 7 4` does not read it; the base adds |
| `segOut_rep_kite_ctl` | positive / negative | `rep` moves the base by `s`; `kite` takes only the flag's branch |
| `sibW_ctl` | positive / negative | bit 0 (from answer word 100) picks node words 6–9, not 2–5; bit 1 picks 2–5; `sK = 0` gives zeros |
| `kflag_ctl`, `kOf_ctl` | positive / negative | `'N'`, `'P'` set the flag, `'L'` does not; only the low byte counts; the two ladders differ (level 0's `logN` is 18 and 20) |
| `trWf_ctl` | positive / negative | a squeeze item gives 10 words, an 8-byte absorb 11; the first is the constant `toWord 40` |
| `qOk_ctl`, `prevInv_ctl` | positive / negative | the phase table passes `qOk`; a `queries` phase without its `P2` fails; `PrevInv` constrains after a `P2` phase |
| `witWords_tag`, `outIR_tag` | negative | the output starts with the node tag `1` (not a leaf witness) |
| `addrS_ctl`, `addrL_ctl` | positive | stream word 1 is the next cell, word 2 the next row (`+2^18`), word 8 the next block (`+4`); L word 2 is the next row, word 128 two cells on |
| `okSeg_ctl` | positive / negative | the program's segments pass `okSeg`; a count of `2^32` or `per = 0` fails |
| `outIR_any` | positive (universal) | `outIR_out`'s hypothesis holds on every heap, with `w` read at `ob0` |
| `ext_node`, `E_node`, `decNode_out` | universal | for every log, transcript and proof with Part 19's hypotheses |

The controls are statements about the pure segments, or follow from the `_sem` lemmas. None is
a concrete machine run (S-H2k's ≈ 185 ms per operation).

### 5. Checks

- **Build**: the whole entry plus the new modules,
  `lake build FR FRXNodeRun FRNodeRead FRNodeReadW FRNodeReadLayout FRNodeReadS FRNodeReadP FRXOut FRXOutRun`,
  is green in `logs/fr-build-SH2l` (2,371 jobs; 4 min 59 s wall on the shared VM;
  `logs/S-H2/build21.{out,log}`). Re-checked on HEAD `d332644`: green, 2,374 jobs
  (`build21b`). The tree is a HEAD snapshot (`snap.sh`); my modules are symlinks.
- **Axioms** (`logs/S-H2/axioms21.log`):
  - these depend on `propext, Classical.choice, Quot.sound`: `computes`, `ext_caps`,
    `ext_node`, `E_node`, `E_leaf`, `cost_le_decLN3`, `cost_le_decLN3_node`, `decOk_decLN3`,
    `decNode_sem`, `decNode_out`, `outIR_out`, `segIR_sem`, `sibIR_sem`, `proof_words`,
    `reassemble_size`, `witWords_readWit`, `readWit_fits`, `logWords_trSeg`,
    `sigWords_sigSeg`, `traceKind_lvl`, `addrS_ctl`, `addrL_ctl`, `outIR_any`, `outIR_tag`;
  - the `decide` facts and controls (`cost_outIR`, `outs_outIR`, `sizeIR_outIR`,
    `segLen_pSeg`, `segOut_*_ctl`, `sibW_ctl`, `kOf_ctl`, `trWf_ctl`, `qOk_ctl`, `okSeg_ctl`)
    depend on `propext`; `kflag_ctl` and `prevInv_ctl` on `propext, Quot.sound`.
- **Source rule**: 152 files, 0 findings (`logs/S-H2/source21.log`). There is no `sorry`.
- **Sequential profile** (`taskset -c 0`, `-DElab.async=false`, `logs/S-H2/*.21.{profile,time}`):

  | Module | wall | max RSS | type checking (entries ≥ 0.1 s) |
  |---|---|---|---|
  | `FRNodeReadS` (new) | 13.1 s | 2.75 GB | 2.33 s, one entry (a `decide +kernel` over the phase table) |
  | `FRNodeReadP` (new) | 21.3 s | 3.02 GB | 5.8 s, of which one entry is 4.94 s (the decided phase-table facts, `qOk_restSh` / `segLen_pSeg`) |
  | `FRXOut` (new) | 57.7 s | 2.60 GB | 0.2 s; elaboration dominates (`sibP_sem`, `segIR_sem`) |
  | `FRXOutRun` (new) | 16.0 s | 2.54 GB | 3.3 s (the four exact `decide +kernel` facts, ≈ 0.6 s each) |
  | `FRXNode` | 28.3 s (was 26.6 s) | 3.21 GB | 6.0 s, of which 4.4 s is `toyFin_run` (unchanged) |
  | `FRXNodeRun` | 7.0 s | 2.63 GB | below 0.1 s |
  | `FRNodeReadW` | 14.9 s | 2.87 GB | as in Part 20 (`tail_slen_le` now carries the 3.5 s) |
  | `FRXSpec` | 12.4 s | 2.73 GB | 0.38 s (the toy runs, with the new `decSnark` compiled in) |

### 6. Deviations and choices

1. **No gather.** The handover planned to copy each slot's stream into `obL`. Instead `outIR`
   reads every word through one computed load (`addrW`). Both shapes are affine in the bits of
   the index, so `outIR` stores nothing. Its heap frame is then `LoK`'s, and `decNode_sem`
   keeps its statement. The cost is ≈ 38 steps per output word, 2.2·10^7 in all.
2. **`decNode_sem`'s proof moved to `decF0_sem`** (same statement, about the decode
   `decF0`). `decNode_sem` keeps its statement about the new `decNode`, from `decF0_sem` and
   `outIR`'s frame. `cost_decNode` and `outs_decNode` changed: they are equations about
   `decNode`'s body, which grew.
3. **The witness function is stated as `fun e => (msgOf .N30 L es 0 (e % 64) (e / 64)).f₀`.**
   This is `fF .N30 L es` once `fTab` is unfolded (`(lvl .N30 0).rows = 64`). The `FRX`
   modules do not import `FRSoundnessPIOP`, where `fF` lives. `final` can rewrite with
   `fF`'s definition.
4. **The child's kind at run time.** `sibling` and `posOf` use the child's ladder
   (`traceKind`). `outIR` reads it from stream word 10 (`kflag`), and the sibling segment is a
   `kite` between `ladder30` and `ladder32`. A byte that is no kind byte gives `L32`, as in
   `traceKind`.
5. **The length words are constants** (`toWord qlen`, the ruling), in the trace (`tItems`) and
   for the proof (`toWord piSize`).

### 7. What remains (in order)

1. **The links on `final`'s side** (Part 19 §8 item 2, unchanged): `FinalLaw` must supply
   `E_node`'s transcript hypotheses from `runLog = some true` (S-G2/S-G3). It then gets
   `E c π L = some (FR.readWit (fF .N30 L es))`.
2. **`FR.lean` imports.** The worktree's `FR.lean` (INT-3) already imports `FRNodeReadLayout`,
   `FRNodeRead`, `FRNodeReadW` and `FRXNodeRun`. Add **`FRNodeReadS`, `FRNodeReadP`, `FRXOut`,
   `FRXOutRun`**. They are already reached through `FRXExt → FRXNode`, so the build does not
   need them; listing them is for the module list.
3. Optional golf: `FRXOut`'s register frames repeat a pattern (`simp only [names]; omega`
   dischargers, `wrL` membership).

### 8. Pitfalls (also in the journal, items 49–53)

- Close goals of the form `[] ++ big = big`, or arithmetic over `cost decN t`, with
  `List.nil_append` or with `generalize` and `omega`. **Not `rfl`**: the kernel unfolds the big
  side (deep recursion or a timeout at the declaration).
- In a long `runPrims` `rd` chain, discharge with `simp only [register names]; omega` only. A
  `decide` discharger evaluates the array size. Read the heap through
  `rd_runPrims_of_not_writes`.
- `exact lemma` against a goal stated with a folded program (`segIR ap d (.cp o n)`) timed out
  in unification: `rw [segIR, segOut]` first.

## Part 22 (track S-H2m): `E` as the program's denotation (revision 3.17 O3); stopped at the coordinator's request

**Status.** I stopped at a clean point when the coordinator ruled that core PR #20 (a 128 MiB
`Computes` domain "closed under extraction in the kernel", no `proofCap` in `acc`, a new
knowledge-soundness definition) probably supersedes 3.17's O3 ruling. Items 1 and 2 are done.
Item 3 (`FRSoundnessExtE`) and items 4–5 (the out-of-domain controls, the profiles, the
executable probe) were **not started**. The build is green, and nothing was committed.

### 1. What changed (6 files, +104 / −57 lines)

| File | Change |
|---|---|
| `FRXComputes` | New: **`den mem mpw P inp`**, `semXIR`'s output from `initSt (mem + mpw·t)`: a total function with no fuel. **`Eden mem mpw P c π L := decodeWit (den … (extractorInput c π L))`**. **`den_of_run`**: whenever `(toProg mem mpw P).run inp f = some o`, then `o = den …`. It holds for every fuel and needs no loop bound. The proof uses `runs_body`, the contract's `run_of_runs`, `run_eq` and `exec_mono`. **`computes_Eof` is restated** for `Eden`: halting within the fuel with at most `outCap` words on the domain gives `Computes (toProg …) (Eden …) fuel`. `Eof` was removed. `computesWith` now targets `Eden memX mpwX (extIRWith dec)`. |
| `FRXExt` | **`E := Eden memX mpwX (extIRWith decSnark)`** (B-8, 3.17). `ext`, `computes : Computes ext E fuel` and `ext_caps` keep their statements. `computes`' proof is unchanged (`computesWith`). |
| `FRXSpec` | `E_W` and `E_bad` are now stated over `Eden`, and proved by `run_W`/`run_bad_tape` + `den_of_run`. Their hypotheses are unchanged: only `π.size < 2^64`, nothing about the log. `ext_W`, `ext_bad` and `ext_encode` keep their statements. |
| `FRXLeaf` | New: **`den_leaf`**, the denotation on a leaf proof, **on every log**. It is `run_leaf`'s old proof minus the loop bound and the run. `run_leaf` keeps its statement and is now `halts_with` + `den_of_run` + `den_leaf`. **`E_leaf` is restated without `hq`/`ht`**. |
| `FRXNodeRun` | `E_node`'s proof is now `ext_node` + `den_of_run`. **Its statement is unchanged; it keeps `hq`/`ht`** (finding O3′). |
| `FRSoundnessExtAll` | A minimal proof repair: `X.E_leaf c π L hk hkN` (the two domain arguments dropped). |

**Statement changes, all as 3.17 rules:**
- `E`'s definition.
- `computes_Eof` (`Eof` → `Eden`; new hypotheses `hmem`, `hP`).
- `computesWith`'s target.
- `E_W`'s and `E_bad`'s left-hand sides.
- `E_leaf` (no domain hypotheses).

`ext`, `computes`, `ext_caps`, the cost lemmas, `run_leaf`, `ext_node`, `ext_W`, `ext_bad` and
`E_node` are unchanged.

### 2. Item 1: `semXIR` is total and computable, but it is the 64-bit machine (finding O3′)

**Total and computable.** `semXIR` is structural recursion on `XIR`, and `iterL` is recursion
on `ℕ`. There is no `partial` and no fuel. A loop runs `(rd M n).toNat < 2^64` times. `E` is a
compiled `def`: `FRXExt` builds with no `noncomputable`, and every ingredient is computable
(`decodeWit`, `extractorInput`, `initSt`'s `Array.replicate`). The executable probe (item 5) was
not run.

**The 3.17 premise does not hold.** The ruling says that "`final` follows from `ext_good_tape`,
which is stated over `semXIR` and is domain-free". That is false for the node case:
- `semXIR` is the machine's exact semantics (`compile_correct`). Every tape read is
  `I.getD (rd M a).toNat`, where `rd M a` is a 64-bit word. So **no tape word at position
  `2^64` or later is ever read**, and counts such as `toWord |L|` wrap.
- The node case's semantic lemmas take `Dom` essentially: `read_spec`, `look_spec`,
  `idxIR_sorted`, `nodeBody_sem`, `colIR_sem`, `posBody_sem`, and with them `decNode_sem`,
  `decNode_out` and `ext_node`. For example, `Dom.small : |L| < 2^62` and `tp_posL`.
- The contract's `step` lets a log hold 2^62 fresh junk entries before an honest chain while
  `μ < 1`. On such a log the chain lies beyond tape word `2^64`. The denotation cannot see it,
  so neither `E := semXIR` nor any compiled program can extract there.
- `hOut` can therefore not be discharged for node proofs. It **can** be discharged for `W`,
  `bad` and leaf proofs, because `E_W`, `E_bad` and `E_leaf` are now domain-free.

The contract states this itself (`Security.lean`: "on longer logs `E` is unconstrained and may be
a non-constructive choice", `choice_certificate`).

**Fixes I see (not implemented):**
- (a) A contract-side change, which PR #20 may make: a domain closed under extraction.
- (b) `E := if InDom then Eden … else Eₒ`, with `Eₒ` a *computable* search over the finite space
  of witnesses for `Rel (accV (vkOf π)) c`. `acc` is a `Bool` and bounds the proof, the trace and
  the queries. `SigOk`'s bounds on `σ` would need checking.
- (c) A pure computable twin of the extractor, with `ℕ` indices.

### 3. What is half-done (in order, if 3.17 still stands)

1. `FRSoundnessExtE`: `ExtIfaceE`, `extIfaceE_of`, `hExt_of_ifaceE`, `finalLaw_ofE` and
   `kstate_front_ofEN`. The domain hypothesis would be `kindOf π = .snark .N30 → InDom c π L`, and
   `hOut` would shrink to a node-only `hOutN`. This needs (b) or (c) to close.
2. Controls:
   - positive: `E` on a `W` or leaf proof with a log holding a `2^64`-byte query (`¬ InDom` from
     `not_inDom_of_big`);
   - negative: `E_bad` on every log, and a blindness lemma (`semXIR` depends only on the tape's
     words below `2^64`, so `E c π (J ++ [e₁]) = E c π (J ++ [e₂])` when `J`'s tape has at least
     `2^64` words and the two queries have the same size).
3. Sequential profiles of `FRXComputes`, `FRXLeaf`, `FRXSpec` and `FRXNodeRun`; a compiled
   executable that imports `FRXExt` and references `FR.X.E`.

### 4. Checks

- `lake build FR FRSoundnessExtAll FRXNodeRun` is green (2,405 jobs) in `logs/fr-build-SH2m`, a
  HEAD `0e9460b` snapshot with my modules symlinked.
- **Axioms** (`logs/S-H2/axioms22.log`): `computes`, `computes_Eof`, `den_of_run`, `ext_caps`,
  `E_leaf`, `den_leaf`, `run_leaf`, `E_node`, `ext_W`, `ext_bad`, `ext_encode`, `extIfaceR_of` and
  `kstate_front_ofE` each depend on `[propext, Classical.choice, Quot.sound]` only.
- **Source rule** (`logs/S-H2/source22.log`): 183 files, 0 findings.
- **Names** `den`, `Eden`, `den_of_run`, `den_leaf`: grepped across `FR*.lean`, no clash.
- **Imports for `FR.lean`:** none new.

## Part 23 (track S-H2n): B-15, the search branch; `hOut` and `hWB` closed

**Status.** All four items are done. `lake build FR` is green against `logs/org20` (2,410 jobs,
`logs/S-H2n/build-final.log`). Nothing was committed. The new route `kstate_front_ofE'`
(`FRSoundnessExtE`) has neither `hOut` nor `hWB`. Its hypotheses are `hRes` (S-N1 O1/O2) and
`kstate_front_of`'s front obligations, plus `hE : S.E = X.E S.acc`.

### 1. Finiteness (item 1)

The witness space of `Rel (S.acc vk) c` is finite under the contract's types. No obstruction was
found.
- **Leaf:** a digest `s` and `n ≤ chainCap` (`Rel`).
- **Node:** two digests and two signed proofs. `Submission.acc` bounds each proof:
  - `|π| < 2^64`;
  - `|tr| ≤ S.qV`, and `S.qV ≤ 2^16` by the certificate's cap;
  - each query is at most `queryCap` bytes, and each answer is a digest;
  - `SigOk` fixes `σ`: `idx < 2^16`, 133 chain values, 16 path digests.

`SFits`/`WFits` (`FRXSearch`) name these bounds. **`sFits_of_acc`** derives them from
`S.acc vk c p = true` when `S.qV ≤ qMax = 2^16`.

### 2. What was built

| File | loc (code) | Change |
|---|---|---|
| `FRXSearch` (new) | 198 | **Finders** `Finder α := (α → Option Wit) → Option Wit`: the first `some` of a test over a fixed enumeration. Built from `fRet`/`fBind`/`fOr`/`fNat`/`fListN`/`fListLe`, with `Sound` and `Covers` rules. They never build a list of candidates, so the compiled code has no large closed term (the compiler would evaluate one at program start). **`fWit`**: the leaves, then the nodes within `acc`'s bounds. **`relDec`/`relDec_iff`**: `Rel` decided. **`search A vk c`**: `fWit` tested by `relDec (A vk) c`. **`search_sound`**, **`search_spec`** (a witness within the bounds exists ⇒ the search returns one), `search_spec_acc` (for an `A` that implies the bounds), `search_none`, `sFits_of_acc`, `wFits_of_rel`. Controls: §4. |
| `FRXExt` | 44 | **`Ed`** (the old `E`: `Eden memX mpwX (extIRWith decSnark)`). **`InDomE`** (decidable): `|π| ≤ 8·outCap`, queries `< 2^64` bytes, tape `≤ 2^64` words. **`Eout A`** by kind: `W` → `WitnessSending.decode π`; a node SNARK → `search A (vkOf π) c`; a leaf SNARK → `Ed`; `bad` → `none`. **`E A := if InDomE then Ed else Eout A`**. Also `E_of_dom`, `E_of_not_dom`, `size_snarkX`, `size_snark_le`, `E_snark_leaf`, `E_snark_node`. **`computes A : Computes ext (E A) fuel`**, from `computesWith` with `E A = Ed` on the domain. |
| `FRXSpec` | 207 | **`ext_W A`: `E A c π L = decode π` on every `W` proof**, with no size bound (`E_W` on the domain, `Eout` outside it). **`ext_bad A`** holds on every size. `ext_encode A` no longer needs `hs`. `E_W`/`E_bad` over `Eden` are unchanged. |
| `FRXLeaf` | 133 | `E_leaf A`: proof via `E_snark_leaf`, then the old proof. |
| `FRXNodeRun` | 120 | `E_node A`: proof via `E_of_dom` (a SNARK has `piSize ≤ 8·outCap`), then the old proof. New **`E_node_out`**: outside the domain, a node SNARK, `A` implying the bounds and some witness of `Rel (A (vkOf π)) c` ⇒ `E` returns a witness. |
| `FRSoundnessExtE` (new) | 151 | **`wBeyond_E`**; `ExtIfaceE` (`ExtIfaceR` without `InDom`); `extIfaceR_of_E`; **`extIfaceE_of`**; `hExt_of_ifaceE`, `finalLaw_ofE` (`hExt_of_ifaceR`/`finalLaw_ofR` without the domain split); **`kstate_front_ofE'`**; controls `extIfaceE_false`, `extIfaceE_W`, `hE_of_accV`. |
| `FRSoundnessAcc`, `FRSoundnessExtAll`, `FRSoundnessExtLinks` | 73 / 84 / 70 | Repairs for `X.E A`. See §3. |
| `FR` | +1 | `import FRSoundnessExtE`. |

**How `extIfaceE_of` covers the out-of-domain node.** On the domain it is `extIfaceR_of`.
Outside it:
- **Leaf:** `E_leaf` (domain-free).
- **Node:** `E_node_out` with `A := S.acc`, which needs two things:
  - the bounds, from `sFits_of_acc`;
  - a witness, `readWit (fF .N30 L es)`. It is one by `rel_readWit` + `acc_eq`, which use no
    domain bound, under the key `vkOf π = vk` (`vkOf_of_run`).

So the existence comes from the decode argument already in the chain. **No new S-G/S-N lemma
is needed**, and no named hypothesis was left.

### 3. Statement changes (every one under B-15)

- `X.E`: new definition, and it takes `A`. On the domain, `E A = Ed` is the old `E`.
- `computes`: now `∀ A, Computes ext (E A) fuel`.
- `ext_W`: takes `A`; **`hπ` dropped** (it is now true on every size; this closes `WBeyond`).
- `ext_bad`: takes `A`; `hπ` dropped.
- `ext_encode`: takes `A`; `hs` dropped.
- `E_leaf`, `E_node`: take `A`. Their hypotheses are unchanged.
- `FRSoundnessExtLinks.E_node_of_run`: gains an implicit `{A}` in the conclusion `X.E A …`.
- `hE : S.E = X.E` → `{A} (hE : S.E = X.E A)` in:
  - `FRSoundnessAcc.hAcc_of_E`, `finalLaw_of_run`;
  - `FRSoundnessExtAll.extIfaceR_of`, `kstate_front_ofE`.

  These old routes still carry `hWB`/`hOut` and are kept unchanged otherwise. Their proofs only
  pass `A` through.

Unchanged: `ext`, `ext_caps`, `Eden`, `E_W`, `E_bad`, `computesWith`, `run_leaf`, `ext_node`, and
everything in `FRSoundnessExtR`/`FRSoundnessAccRun`.

### 4. Controls

- `FRXSearch.search_acceptAll` (**positive**): with `acc` accepting everything, the search
  returns a witness of `nodeStmt d d`. It goes through `search_spec` with the witness
  `node d d signed₀ signed₀`, so no hash is evaluated.
- `search_rejectAll_node` (**negative**): with `acc` rejecting everything, the search never
  returns a node witness.
- `search_none`: no witness, so the result is `none`.
  - A concrete `c` with no witness at all cannot be exhibited: the leaf branch covers every value
    of `leafStmt`.
  - So the negative toy is evaluated in the kernel instead: `toy_found`
    (`fNat 3 (toyTest d 1) = some (.leaf d 1)`) and `toy_none` (`fNat 3 (toyTest d 5) = none`),
    both by `rfl`, with no axioms.
- `FRSoundnessExtE`:
  - `extIfaceE_false` (positive);
  - `extIfaceE_W` (negative: a `W` proof has no run link);
  - `hE_of_accV`: `hE` is satisfiable without self-reference. An `S` whose `E` is
    `X.E (accV impl fin)` meets `S.E = X.E S.acc`.
- The old controls still hold: `ext_encode` (positive), `ext_bad` (negative), `toy_W`, `toy_bad`.

### 5. Checks

- **Build:** `lake build FR` green (`logs/S-H2n/build-final.log`).
- **Axioms:** `logs/S-H2n/axioms.log`. Every listed declaration uses only `propext`,
  `Classical.choice` and `Quot.sound` (or a subset). The list:
  - `computes`, `E_node`, `E_node_out`, `E_leaf`, `ext_W` (= the restated `E_W`), `ext_bad`,
    `ext_encode`;
  - `search_spec*`, `search_sound`, `search_none`, `sFits_of_acc`, the search controls;
  - `wBeyond_E`, `extIfaceE_of`, `finalLaw_ofE`, `kstate_front_ofE'`;
  - the repaired `kstate_front_ofE`, `extIfaceR_of`, `E_node_of_run`, `finalLaw_of_run`;
  - `hE_of_accV`.
- **Source rule:** `python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`
  gives 188 files, 0 findings (`logs/S-H2n/source.log`).
- **Compiled executable:** `logs/fr-build-SH2n/probe/Probe.lean` (outside the entry) does
  `import FR`.
  - It calls `FR.X.E`/`FR.X.Eout` and references `FR.X.search`.
  - `lake build probe` is green: 4,819 jobs, 186 C objects compiled
    (`logs/S-H2n/probe-build.log`).
  - The run (`logs/S-H2n/probe-run.log`) gives: `Eout` on a `W` proof `true`; `E` on a `W` proof
    in domain (the denotation, a 2^26-word memory) `true`; `E` on a `bad` proof `false`. It took
    47 s wall at 1.1 GB RSS. Module start-up is not delayed by the search: there is no large
    closed term.
- **Names:** every new name was grepped across `FR*.lean`.
  - Clashes renamed: `relB` (`FRVIRFinalsSF`) → `relDec`; the finder rules (`sound_bind` in
    `FRBlake2sCompress`) → `sound_fBind` and so on.
  - `Rel` in `FR.X` resolves to another `Rel`, so `FRXNodeRun` writes `RecursionFast.Rel`.
- **Sequential profiles** (`-DElab.async=false --profile`, one core, `logs/S-H2n/prof-*.log`,
  `prof-summary.txt`). Wall time includes about 5 s of import.

  | Module | Wall | Kernel |
  |---|---|---|
  | `FRXSearch` | 6.0 s | 43 ms |
  | `FRXExt` | 6.2 s | 12 ms |
  | `FRXSpec` | 13.1 s | 2.27 s (the old toy runs) |
  | `FRXLeaf` | 9.5 s | 139 ms |
  | `FRXNodeRun` | 7.3 s | 77 ms |
  | `FRSoundnessExtE` | 7.2 s | 102 ms |
  | the repaired modules | 6.1–7.6 s each | — |

### 6. Deviations from the blueprint (changes requested of B-15's text)

1. **`E`'s out-of-domain branch dispatches on the kind**, where B-15 says just "else
   `E_search`".
   - The search's key is `vkOf π`. It is the verifier's key only on an accepted node run
     (`vkOf_of_run`).
   - A `W` proof's bytes `16…47` are arbitrary, so a search under `vkOf π` could miss the
     KS game's `vk`. A leaf SNARK's search could return a node witness for the wrong key.
   - Both kinds have a domain-free witness: `W` → `decode` (this is what closes `WBeyond`), and
     a leaf → the denotation.
   - Suggested text: "`E := if InDom then E_den else E_out`, with `E_out` = `decode` on `W`,
     `E_search` under `vkOf π` on a node SNARK, `E_den` on a leaf SNARK, and `none` on `bad`."
2. **`E` is parametric in the acceptance `A`** that the search tests. The verifier is still
   parametric (`finPf`, `lRows`, `κs₀`). The certificate instantiates `A := accV implC finC`,
   and then `S.E = X.E S.acc` (`hE_of_accV`).
3. **The trace bound in the enumeration is the certificate's `2^16`**, not the entry's `qV`. This
   keeps `FRXSearch` independent of the verifier modules, and the enumeration covers every
   `qV ≤ 2^16`.
4. **`InDomE` (in `FR.X`) and `FR.Snd.InDom`** are both kept.
   - `InDomE = (|π| ≤ 8·outCap) ∧ InDom`.
   - On a SNARK the first conjunct holds, because `piSize ≤ 8·outCap`. So `E_node` keeps
     exactly its hypotheses.

### 7. Open questions / what is left for S-H2

- **Moving the old routes (orchestrator's call).** The old `hWB`/`hOut` routes
  (`kstate_front_ofE`, `kstate_front_ofR`, `finalLaw_of_run`, …) are kept. The integration can
  move to `kstate_front_ofE'` and retire them.
- **The new kinds (S-0′'s `A`/`N4`/`N8`).** `Eout` uses `Kind.isNode`, so a new node kind
  searches automatically. Two pieces must then be generalised from `.N30`:
  - `E_node_out`'s caller in `extIfaceE_of`;
  - the node decoding over `1 + k` children (blueprint S-H2 entry).
- **`hRes`** (S-N1 O1/O2, the node circuit's residual) is unchanged and is not part of this track.

## Part 24 (track S-H3): the revision 4.1 extractor `E4X`: dispatch, aggregate, `computes4`, the frame's laws; the node decoder is over budget

**Status.** HEAD `7e14be6`, build tree `logs/fr-build-SH3` (copy of `fr-build-SG13`, `logs/org20`;
`MINE.txt` = `FRX4Prog FRX4Ext`), logs `logs/S-H3/`. Nothing committed. No existing module or
statement was edited; the two modules are new, in namespace `FR.X.X4`.

| Item | State |
|---|---|
| 1. Plan | **Done** (journal 61). |
| 2. Kind dispatch A / N2 / N4 / N8 / W / bad, cost within the fuel | **Done.** The node branch `nd` is a parameter under `DecOk4` (cost within `decBudget`). |
| 3. The aggregate leaf | **Done**, on every proof size (`den4_agg`, `E4X_agg`). |
| 4. The node case (decode `f⁽⁰⁾` at `m`, output 1 + k children) | **Blocked: 3.x's decoder exceeds the contract's budget at `m = 31/32`** (F1). Not started. |
| 5. `computes4`; B-15's out-of-domain dispatch | **Done** (`computes4`, `Eout4`). |
| 6. The node law in `FRSoundness4Frame`'s form | **Done as an interface**: `NodeDec4` (the links and the cell map are parameters), `nodeExt_E4X`, `ks4_E4X`. |

### F1. The node decoder does not fit the fuel at revision 4.1's node sizes (blocker)

`cost_decLvIR`'s exact formula, per level of `ladderOf m` (`logs/S-H3/fuel-check.{py,txt}`):

| `m` (kinds) | five levels | level 0 | against `B t = 2^48 + 2^16 t` |
|---|---|---|---|
| 30 (3.x `N30`) | 1.41·10^14 = `2^47.00` | 1.40·10^14 | fits (claim.json `3·2^46`) |
| 31 (`N2`) | 5.63·10^14 = `2^49.00` | 5.60·10^14 | **2.0× over `2^48`** |
| 32 (`N4`, `N8`) | 2.25·10^15 = `2^51.00` | 2.24·10^15 | **8.0× over `2^48`** |

Level 0's barycentric interpolation (`baryIR`) costs `k²·(1363 + 106·rows)` with `k = 2^(m−13)`. It
is quadratic, and `k` doubles per `m`. The per-word term cannot pay for it: an extractable node's log
holds the level-0 columns, `t ≈ 2^27` words, so `2^16 t ≈ 2^43`. The contract's `2^48` assumes a
quasi-linear decoder (`Extractor.lean`: "about `2^29` symbols, `2^38.7` field operations").

**Options (coordinator's call):**
- (i) A quasi-linear level-0 erasure decoder: an erasure locator by a subproduct tree, coset FFTs,
  pointwise division, about 10^12 steps. It is a new program with new proofs.
- (ii) Decode only what the output reads. H's message slots are rows 4–7 of level 0
  (`e mod 64 ∈ {4..7}`), so the output needs only those rows. Two changes make this possible:
  - S-E places every signature value the output needs in H's WOTS and path blocks, not in L. L's
    cells spread over all 64 rows.
  - A cheaper `baryIR` inner loop: one batched inversion, not one `invF` per pair. The per-pair cost
    1,363 is mostly the inversion.

  At `m = 32` this gives about 1.6·10^14 (estimate). It changes `decLvIR`/`baryIR` and their proofs.
- (iii) A larger `ell0` for nodes. Ruled out: `ell0 = 6` is S-D3's ruling, and level 0 at `m = 32`
  would need about `2^11` rows.

Until then the certificate's branch is `ndNone` (no output): `E4X_ndNone_node` (in the domain a node
proof extracts `none`). `NodeDec4` states what the decoder must meet.

### 1. Files (`loc.py`, `logs/S-H3/loc.txt`)

| File | total / code / thm | Content |
|---|---|---|
| `FRX4Prog` (new) | 278 / 169 / 26 | Registers `rIsA rIsN rNZ rMk` (248–251). `isW`, `eqPs`, `orPs`, `normPs`, `finPs`, `szPs`, **`kindPs4`**, `parse4`, `outW`, **`aggIR`**, **`ext4IRWith nd`**, **`DecOk4`**, `ext4With`, `ndNone`, `decOk4_ndNone`, **`ext4`**. `wf_*`, `cost_outW`/`cost_aggIR` (11/63), `cost_ext4IRWith` (`≤ 200 + cost nd + 8t`), `sizeIR_ext4IRWith`, **`fuel_covers4`**, `size_ext4With`. The parse's lemmas `runPrims_append`, `rd_eqPs`/`rd_orPs`/`rd_szPs`/`rd_normPs`/`rd_finPs`, `parse4_M`, **`parse4_sz/len/A/N/K`**. |
| `FRX4Ext` (new) | 742 / 543 / 61 | Packed windows on every size: `ofLE_zeros`, `packBytes_pad`, `bytesAt_pad`, **`packBytes_bytesAt'`**, `packBytes_bytesAt4`, `bytesAt_succ`, `ofLE_bytesAt`, `rdLE64_eq`, `rdLE64_lt`, `toWord_rdLE64`. **`aggLeaf`**, **`aggWit_eq`**. Kinds: `kindOf4_eq`, `kindOf4_agg/node/W/bad`, `nodeOfByte_eq`, `segOfByte_eq`, `pos_of_byte`. Flags: `tape4`, `bOf_tape`, `st1`, `flagK_W`, **`flags`**, `isW_sz`. Denotations: `br4`, `den4_split`, **`den4_W`**, **`den4_bad`**, **`den4_node`**, `outW_sem`, `mask_word`, **`den4_agg`**. **`Ed4`**, **`Eout4`**, **`E4X`**, `E4X_W/agg/bad/node/node_out`, **`extOff_E4X`**. `boundsOk_br4`, **`halts4`**, **`computes4`**, `ext4_caps`. **`NodeDec4`**, `E4X_node_dec`, **`nodeExt_E4X`**, **`ks4_E4X`**. Controls (§4). |

### 2. The program and `E4X`

```
ext4IRWith nd := parse4 ; ite rIsK (ite rIsA aggIR (ite rIsN (ite rIsSz nd skip) skip)) wIR
rIsK = (byte ∈ {'A', N2, N4, N8, L30, L31, L32}) ∧ |π| ≠ 0,  rIsSz = (|π| = 798,192)
aggIR := out 0 ; out (w8·[64 < |π|]) ; … ; out (w11·[88 < |π|]) ; out (w1·[8 < |π|])    (wj = tape word 5 + j)
E4X nd A c π L := if InDomE c π L then Ed4 nd c π L else Eout4 A c π L
Eout4: W ↦ decode π,  A ↦ some (aggLeaf π),  node ↦ search A (vkOf π) c,  bad ↦ none
aggLeaf π := .leaf (bytesAt π 64 32) (rdLE64 π 8)
```

- **The empty proof.** `rIsK` is cleared on an empty proof. Tape word 5 is then the log's first word,
  and without the clear an `'A'` there would output a leaf where `decode π = none` (3.x did not need
  this).
- **The mask.** A short aggregate proof reads zeros where the tape already holds the log
  (`mask_word`). `packBytes_bytesAt'` and `toWord_rdLE64` hold on every size, so `den4_agg` needs only
  `|π| < 2^64`.
- **Statements.**
  - `den4_W`: `den … = packBytes π` on every `W` proof (any size `< 2^64`, every log).
  - `den4_bad`: `den … = []`.
  - `den4_agg`: `den … = witWords (aggLeaf π)`.
  - `den4_node`: the node branch's output from the parse's state `st1`.
  - `halts4`: the program halts within `fuel` with at most `outCap` words on every domain tape. `W`:
    `⌈|π|/8⌉ ≤ 2^24`; `A`: 6 words; a node: `outs_le` + `DecOk4.outs`.
  - `computes4 hnd A : Computes (ext4With nd) (E4X nd A) fuel`.
  - `ext4_caps`: `fuel ≤ B`, size `≤ progCap`.
- **`extOff_E4X nd A : Rev4.ExtOff (E4X nd A)`** holds on every proof size, through `aggWit_eq`
  (`aggWit = some (s, n) → aggLeaf π = .leaf s n`; segments are `798,192 ≥ 48` bytes).
- **The node law.**
  - `NodeDec4 nd` has three fields:
    - `Links κ L es π c` (S-H2's `E_node` hypotheses at revision 4.1, a parameter);
    - `readW κ L es` (the witness read off `f⁽⁰⁾`, a parameter: the revision 4.1 cell map is S-E's);
    - `out`: under the links, on the domain, `nd` outputs `witWords (readW κ L es)`, and the witness
      fits.
  - `nodeExt_E4X D hq hN hL : NodeExtLog Vnode vk Good (E4X nd S.acc) (Rel (S.acc vk))`:
    - outside the domain, from `NodeSoundLog` via `search_spec_acc` (as `nodeExt_E4`);
    - on the domain, from `D` and S-G's `hL` (an accepted node run on a good log has `es` with
      `Links` and `Rel c (readW κ L es)`).
  - `ks4_E4X` is `ks4_of` at `S.E = E4X nd S.acc`.

### 3. Costs (exact theorems)

| part | steps | theorem |
|---|---|---|
| `outW j` | 11 | `cost_outW` |
| `aggIR` | 63 | `cost_aggIR` |
| program | `≤ 200 + cost nd t + 8t` | `cost_ext4IRWith` |
| fuel | `memX + 3t + cost + 8 ≤ 3·2^46 + 2^13 t` whenever `cost nd ≤ decBudget` | `fuel_covers4` |

`claim.json` was checked: `fuel_base = 211,106,232,532,992 = 3·2^46`, `fuel_per_word = 8,192 = 2^13`,
as `FRXProg.fuelBase`/`fuelPerWord`. The memory is 3.x's (`2^26 + 3t`). A decoder at `m = 32` holds
`f⁽⁰⁾`'s `2^25` cells and will need a larger `mem`.

### 4. Controls

| Control | Kind | Shows |
|---|---|---|
| `E4X_encode` | positive | a witness-sending proof is decoded (every `nd`) |
| `E4X_bad_ctl` | negative | a bare `L32` byte, and an `N4` byte of the wrong size, give `none` |
| `aggLeaf_ctl` (`decide +kernel`, 96 bytes) | positive / negative | the toy `'A'` proof is `agg`; `n` is read at bytes 8–15 (`= 5`), not 0–7; the start at byte 64 (`= 7`), byte 63 is not read |
| `E4X_toyA` | positive | `E4X` returns the toy's `aggLeaf` |
| `E4X_ndNone_node` | negative | the certificate's current node branch extracts nothing in the domain |
| `not_nodeDec4_ndNone` | negative | no `NodeDec4 ndNone` has a linked node input: the decode law is not vacuous |
| `nodeDec4_none` | positive | the law holds for any branch when no input is linked: it constrains only linked inputs |
| `den4_*`, `halts4`, `computes4`, `extOff_E4X` | universal | for every log and proof (size `< 2^64`, or the domain) |
| probe run | measurement | the compiled `E4X` (2^26-word denotation) on W: `true`; on a bare segment: `false`; on the toy aggregate: `leaf, s[0] = 7, n = 5` (`probe-run.log`) |

No control is a concrete machine run in the kernel. The toy is a byte-level `decide +kernel` over 96
bytes.

### 5. Checks

- **Build.** `lake build FR FRX4Prog FRX4Ext` is green: 2,430 jobs (`build-final.log`).
- **Axioms** (`axioms.log`, 25 declarations, among them `computes4`, `halts4`, `extOff_E4X`,
  `nodeExt_E4X`, `ks4_E4X`, the `den4_*` and every control): within `propext`, `Classical.choice`,
  `Quot.sound`. There is no `sorryAx`.
- **Source rule.** `python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`: 235
  files, 0 findings (`source-rule.log`).
- **Compiled executable.** `logs/fr-build-SH3/probe/Probe.lean` (outside the entry) imports `FR` and
  `FRX4Ext` and calls `E4X`, `Eout4` and `ext4`.
  - `lake build probe`: 4,859 jobs, green (`probe-build.log`).
  - Run: 49 s, 1.1 GB (`probe-run.log`). Module start-up is not delayed.
  - So `E4X` is computable: nothing is `noncomputable`.
- **Sequential profiles** (`taskset -c 0`, `-DElab.async=false`, `prof-*.log`):
  - `FRX4Prog`: 9.5 s wall (import 3.7 s), kernel 0.42 s, 2.85 GB;
  - `FRX4Ext`: 12.1 s wall (import 3.8 s), kernel 1.26 s, 2.98 GB.
- **Names.** Everything is in `FR.X.X4`. A grep of `FR*.lean` found no other use of the namespace.

### 6. Deviations and choices

1. **The node branch is a parameter** (F1). The brief's items 4 and the decoding half of 6 need a
   decoder within `B t`, and 3.x's is not one at `m = 31/32`.
2. **`NodeDec4.Links` and `readW` are parameters.** 3.x's links (`farL`, `consSet`, `capDig`, `fmAns`
   over `fsQ`) are stated over 3.x's `Kind` and positions. Their revision 4.1 forms come with P4b's
   and R4's ports and S-E's cell map (`FRNodeKinds4`/`FRNodeRows4` have appeared untracked in the
   worktree, from other tracks). The names follow S-H2's `E_node`.
3. **`aggLeaf` reads `π` directly** (bytes 64–95 and 8–15), not through `aggWit`. It agrees with
   `aggWit` whenever `aggWit` is `some` (`aggWit_eq`), and it is total, so the agg branch needs no
   checks. Soundness needs only `ExtOff`'s clause.
4. **One fuel and one memory with 3.x** (`memX`, `fuel`, `decBudget`). `claim.json` is unchanged.

### 7. What remains (in order)

1. **Coordinator: rule on F1** ((i) a quasi-linear level-0 decoder, or (ii) the partial decode plus
   S-E's placement of the signature in H). Everything below waits on it.
2. **The revision 4.1 node decoder `nd`** with `DecOk4` (at a possibly larger `mem`).
   - The read and index carry over; positions come from `phStart4_shift`.
   - `decLevels` at `ladderOf κ.m` per kind needs a kind flag at run time: N2's ladder is
     `ladderOf 31`, N4/N8's `ladderOf 32`.
   - The output `outIR4` covers `1 + k` children. The aggregate child's stream is
     `0x54 ‖ tr₁ ‖ … ‖ tr_k` at H block `chainLenOf seq4` (`N2/N4`) or `aggChainLen 4` (`N8`'s
     second). Segment `i ≥ 2` starts at stream byte `1 + (i − 1)·1,482,751`, which is unaligned
     (shift `(i − 1)·7 mod 8`). It needs a shifted-copy leaf in the segment language, or a realign
     pass into an aligned buffer, after which 3.x's `segIR` applies with linear addressing
     `ap = (0, 1, 1)`. `hdr_A`'s `k`, `n`, `e` come from the statement preimage blocks (S-0′ O-1),
     so this needs S-E's cell map.
   - Then discharge `NodeDec4.out`.
3. **S-G's side `hL`**: the links and `Rel c (readW …)` from an accepted node run (P4b/R4/X4).
4. **`FR.lean`: add `import FRX4Ext`** (orchestrator; it pulls `FRX4Prog`). The certificate can then
   use `S.E := E4X ndNone S.acc`, `S.ext := ext4`, with `computes4 decOk4_ndNone` and
   `ext4_caps decOk4_ndNone`. Its node law stays open until item 2.

### 8. Pitfalls (journal 62)

- A 27-prim `rd` chain times out. Split it into small lists and use `runPrims_append` with
  per-piece lemmas.
- A `BoundsOk … (br4 nd) s` type in a `have` is whnf'd and evaluated on the concrete tape. Make
  `br4` locally irreducible.
- `simp; ring` over 8-term little-endian sums gives a kernel deep recursion under `lake build` only.
  Prove by induction instead.
- `simp` rewrites `byteAt` to `data[·]?`. Generalize the byte before the case analysis on `kindOf4`.

## Part 25 (track S-H4, pass 1): the level-0 interpolation by prefix and suffix products (`FRXLag`); the fuel at revision 4.2; handover

**Status.** HEAD `aa42b2d`, build tree `logs/fr-build-SH4` (copy of `fr-build-SH3`, `logs/org20`;
`MINE` = `FRX4Prog FRX4Ext FRXLag`), logs `logs/S-H4/`. Nothing committed. One new module, `FRXLag`
(namespace `FR.X`); no existing module or statement was edited. Item 1 is half proved (the weights and
values on the machine); items 2–6 are not started. The handover (§6) lists what remains, in order.

### 1. The method, and why it differs from the ruling's wording

The ruling asks for Montgomery's batched inversion in `baryIR`. `FRXLag` does better with the same
structure:

- **The domain is `B64`.** `D x = ofB64 x` (`FRRS.D`). Every difference `D s − D J_u` is the one-word
  `B64` value `s ⊕ J_u`. Its products cost `mulB`, 13 steps, against `mulF`'s 57.
- **No inversion per target.** The Lagrange numerator `Π_{u ≠ t} (s ⊕ J_u)` is the prefix product
  `P_t = Π_{u<t}`, stored by a forward pass, times the suffix product `Q_t = Π_{u>t}`, kept in a
  register by a backward pass. This is Montgomery's pass without its one inversion. The barycentric
  form needs `ℓ(s)⁻¹`; the Lagrange form needs only the product, so there is no case `ℓ(s) = 0`.
- **The weights.** `W_t = (Π_{m ≠ t} (J_t ⊕ J_m))⁻¹` is computed as `Π_m ((J_t ⊕ J_m) ||| [J_t = J_m])`,
  then one `invB` per `t` (`k` in all). It is folded into the values: `Y_c[t] = W_t · y_c(J_t)`, two
  `B64` products per row.
- **Per pair** (target, agreement point): 26 steps for the weight's factor, 29 for the forward pass,
  `46 + 40 C` for the backward pass (`C` rows, each two `B64` products and two `xor`s).

**`cost_lagIR`** (exact): `27 + k (1,122 + 72 C) + k² (101 + 40 C)`. At `C = 4` that is **261 steps per
pair**. 3.x's `baryIR` costs 8,147 on 64 rows; the blueprint estimated 484 for (ii).

### 2. The fuel (`logs/S-H4/fuel-check4.{py,txt}`)

The model uses 3.x's exact per-level components (as `logs/S-H3/fuel-check.py`), with level 0's
interpolation replaced by `lagIR` on 4 rows and its butterflies on 4 rows. Levels 1–4 are either 3.x's
`baryIR` (16 rows) or `lagIR` with `C = 16`:

| `m` (kinds) | five levels, 1–4 by `baryIR` | five levels, 1–4 by `lagIR` | `decBudget` (`2.11·10^14 + 8,176 t`) |
|---|---|---|---|
| 30 | 5.33·10^12 (`2^42.3`) | 4.70·10^12 | 40× under |
| 31 (`N2`) | 2.13·10^13 (`2^44.3`) | 1.88·10^13 | 10–11× under |
| 32 (`N4`, `N8`) | **8.51·10^13 (`2^46.3`)** | **7.50·10^13 (`2^46.1`)** | **2.5–2.8× under** |

Level 0 at `m = 32` is 7.18·10^13; level 1 is 1.3·10^13 by `baryIR` and 3.2·10^12 by `lagIR`. The
reads, the chain, the index and the output are about 10^11 + 2,558 t (3.x's figures, scaled). So
`fuel_base = 3·2^46` stands, and `claim.json` needs no change. The figures are the model's: the
decoder program `nd` is not yet written, so there is no `cost` theorem for it (item 5).

**Levels 1–4 need every row.** Level `i`'s decoded message (all 16 rows) is level `i − 1`'s `nextMsg`:
`msgHIR` reads rows `2(x mod 8)` and `2(x mod 8) + 1` for every `x`. So level `i − 1`'s agreement set
depends on every row of level `i`. Level 0 needs all 64 rows of its *word* for the flags (a linear
cost), and only rows 4–7 of its *message*.

**Memory: `mem = 2^27` is too small (finding F2).** The level-0 decoder holds f⁽⁰⁾'s *codeword*. At
`m = 32` that is 2^20 positions × 64 rows × 2 words = 2^27 words: 3.x stores the whole word at
`colBase` for the flags. The blueprint's 2^27 counts the message (2^25 cells). With the other regions
(level 1's word 2^23, `J`, `P`, `Y`, the flags, `X`/`Y`, the rows) the decoder needs about
2^27 + 2^25 words. So **`memX` must be 2^28**. The fuel cost is 2^28 steps, which is negligible. The
index base moves with it: 3.x hard-codes `memX` in `walkPre` and in the lookups. A streaming read
that folds the 64 rows on the fly would avoid it, but it needs the chain before the read and a new read
program. I do not propose it.

### 3. Files (`loc.py`)

| File | total / code / thm | Content |
|---|---|---|
| `FRXLag` (new) | 920 / 738 / 52 | Registers `lgJ … lgAc` (160–215). `fct`; the program: `wInL`, `yLd`, `ySt`, `yRowL`, `wyMid`, `wyBody`, **`yTabIR`**, `fwdL`, `accRow`, `accIR`, `bwdL`, `stRow`, `stAcc`, `zeroPs`, `tgBody`, `tgIR`, **`lagIR`**. Structure: `wf_lagIR` (with `nw_accIR`, `nw_stAcc`, `nw_invB`), `noLoopT_lagIR`, `outs_lagIR`, `cost_accIR`, `cost_stAcc`, `cost_wyBody`, `cost_tgBody`, **`cost_lagIR`**, `sizeIR_accIR`, `sizeIR_stAcc`. Pure: `jw`, `dif`, `preP`, `sufP`, `wgtB`, `yv`, `lagTerm`, **`lagVal`**, `D_sub_D`, `pre_suf`, `ofB64_prod`, `ofB64_inv`, `jw_inj`, `fct_eq`, **`lagVal_eq`**. Machine: `ld_M`, `inv_set`, `st_rd`, `semB`, `amm_run`, `wInL_sem`, `wLoop_sem`, `yLd_sem`, `ySt_sem`, `yRowL_sem`, `yLoop_sem`, `wyBody_sem`, `wgtJ`, **`yTab_sem`** |

**What is proved.**
- **`lagVal_eq`**: with `J` listed without repeats below `2^20`,
  `lagVal Jl |Jl| s y = interpF D Jl.toFinset y s`. Here `lagVal = Σ_t P_t Q_t (W_t · y(J_t))` is
  exactly what the machine accumulates.
- **`yTab_sem`**: on a layout `regs ≤ jb`, `jb + k ≤ yb`, `yb + 2Ck ≤ cb`, `yTabIR` leaves
  `rdB (yb + 2(Ct + c)) = rdB (cb + cs J_t + 2c₀ + 2c) · W_t` and the same at `+1`, for `t < k`,
  `c < C`. The heap outside `[yb, yb + 2Ck)` is kept.
- **`cost_lagIR`**, `wf_lagIR`, `noLoopT_lagIR`, `outs_lagIR = 0`.

### 4. Checks

- **Build.** `lake build FRXLag FR` is green in `logs/fr-build-SH4`: 2,476 jobs (`build1.log`).
  `FR.lean` does not import `FRXLag`; the orchestrator adds it once `nd` uses it.
- **Axioms** (`axioms.log`, 13 declarations): within `propext`, `Classical.choice`, `Quot.sound`.
  There is no `sorryAx`.
- **Source rule** (`source-rule.log`): 267 files, 1 finding, `FRVIRSpec.lean:259: simproc`. That file
  is G1's work in progress (uncommitted, `git diff` +16 −3). `FRXLag` has no finding.
- **Sequential profile** (`-DElab.async=false`, `prof-FRXLag.log`): 85 s wall, 2.86 GB. The kernel is
  small (the listed type-checking entries are 0.13 s and 0.35 s). Elaboration dominates: three
  `refine`s of 7–11 s each, the `loopK_run` invariants with `by decide`/`omega` arguments, plus
  `nlinarith` (3–4 s each). This must be golfed before the certificate's build budget sees it: replace
  `nlinarith` by stated products, and pass register disequalities as named lemmas.
- **Compiled probe** (`logs/fr-build-SH4/probe/Probe.lean`, outside the entry; it imports `FR`,
  `FRX4Ext` and `FRXLag`):
  - `lake build probe`: 4,951 jobs, green (`probe-build.log`).
  - Run: 5.8 s, 0.9 GB (`probe-run.log`). `E4X` on the S-H3 toys behaves as before.
  - **`lagIR` toy:** 4 targets, rows 1–2 (`c₀ = 1`, `C = 2`), `J = [3, 7, 1, 12]`, run through compiled
    `semXIR` on a 600-word heap. All 8 outputs equal a direct Lagrange interpolation in `F`: `true`.
    The same outputs against rows 0–1 give `false`, so the row window is read.
  - The target `s = 3 = J₀` returns `y(3)`: `true`.
  - This is an empirical check of the half that is not yet proved (the target loop). It is not a
    proof.
  - `snap.sh` now re-adds the `probe` target when it rewrites the lakefile.

### 5. Deviations

1. **Prefix and suffix products, not a batched inversion** (§1). The cost is lower (261 against 484 per
   pair), and there is no inversion and no `ℓ(s) = 0` branch.
2. **`mem` must be 2^28, not 2^27** (§2, F2).
3. **Levels 1–4 may use `lagIR` too.** With `C = 16` it costs a quarter of `baryIR` at level 1. Then one
   interpolation program serves all levels. This also helps step 2 of the retirement plan:
   `FRXBary*` can leave the decoder's closure.

### 6. Handover: what remains, in order

1. **Finish item 1: the target half of `lagIR`** (`FRXLag`; the program and its cost are final):
   - `fwdL_sem`, then the forward loop: `P_t = preP` at `pb + t`, `lgP = preP s k`. The loop stores, so
     state the heap frame outside `[pb, pb + k)`.
   - `accRow_sem`, then `accIR_sem` by induction on `C`:
     `rdF (lgAc + 2c) += smulBase e (rdF (lgX₀ + 2c))`, `lgX += 2C`. Use `amm_run` for the two products
     and two `xor`s on the accumulator words, and `wB_xor`.
   - `bwdL_sem`, then the backward loop. After `j` steps the invariant is
     `Q = sufP (k − j)`, `acc_c = Σ_{t ∈ Ico (k−j) k} lagTerm`, with `lgA`, `lgB`, `lgY` decremented.
   - `stAcc_sem` by induction: the `C` stores at `ob + 2s + 2kc`.
   - `tgBody_sem`, then `tgIR_sem`: the target loop, with output cells for `s < j` and a frame outside
     `[pb, pb + k) ∪ [ob, ob + 2kC)`.
   - **`lagIR_sem`**: `rdF (ob + 2kc + 2s) = lagVal Jl k s (y_{c₀+c})`. Use `yTab_sem`; `yv` is
     `smulBase` of `wgtJ`, by `mulBW_spec` and `mul_comm`.
   - **`lagIR_interp`** through `lagVal_eq`.
   - Pattern: flatten each body with `simp only [body, semXIR_seq, semB]`, generalize innermost-first
     with `⊢`, and name every frame index (journal 65).
2. **Item 2: the level-0 decode at `CKind`.** The 3.x level theorems (`decFront_sem`, `decBack_sem`,
   `decLv_sem`, `level_decode`, `consN`, `flagV_consSet`, `msgH_next`) are stated at `.N30`, with 3.x's
   `Kind`, `lvl`, `wordOf` and `msgOf` (`FRSoundnessTruths`), and on 3.x's fixed memory map.
   - The revision 4.1 truths are T4's `CKind` copies in `FRSoundness4TailTruths` (`msgOf`, `consSet`,
     `decodeL`, `farL`, `sAt` at `phStart4`). Other tracks are editing that file now (uncommitted
     changes in the worktree).
   - Port `level_decode` → `level_decode4` over `CKind`. It is pure: copy and rename, with
     `lv_params` for `CKind.lv`.
   - Then `decBack4` = `scanIR ; lagIR (2^mLog) 4 4 … ; bfRowsIR mLog ob tb 4`, on a memory map record
     parametric in `m` (§2's sizes).
2′. Re-derive `decFront_sem` (the `eq` table, `msg`, `fwdIR ×2`, `flagIR`) on that map, for `CKind`.
   The programs are generic; the statements bind `.N30` and the 3.x constants (`fbF`, `xbM`, `ybM`,
   `eqB`, `obL`, `memX`).
3. **Item 3:** `decLevels4` takes the kind at run time. An `ite` on the node byte chooses
   `ladderOf 31` (`N2`) or `ladderOf 32` (`N4`/`N8`); both branches are the same program at two
   constant sets. Then `memX4 = 2^28`, with the index and read at `memX4`. `readIR` is parametric in
   its base, but `walkPre` hard-codes `memX`: `walkPre4`, `idxIR4`, and the cap offsets at 4.1's
   positions.
4. **Item 4: the output** `outIR4`.
   - It reads the `1 + k` children from rows 4–7 at `ob0` (stream cell `e` is row `4 + e mod 4`,
     column `e / 4`, as `FRBlockStream.elem_slot`). Check S-E12a's block-kind map in `FRNodeCircuit4*`
     (untracked in the worktree).
   - The signature comes from the H fields (`sig_of_H` as a hypothesis).
   - The aggregate child's segments 2–4 need a shifted copy (`(i − 1)·7 mod 8`).
5. **Item 5:** `nd`, `DecOk4 nd` (with `decBudget4` at `memX4`), `NodeDec4.out`, the exact `cost`
   theorem, and `fuel_covers4`.
6. **Item 6:** controls stated from `_sem` lemmas (the probe's toy is a compiled run, not a kernel run).
   Then golf `FRXLag`'s elaboration (§4).

## Part 26 (track S-H4, pass 2): `lagIR` proved; one level's decode at revision 4.1's kinds on a parametric memory map; handover

**Status.** Started at HEAD `a91d355`, re-snapshotted on `1263569` (after G2 and RET-2 landed). Build tree
`logs/fr-build-SH4b` (copy of `fr-build-SH4`; `MINE` = `FRXLag FRXLagT FRXDec4Level FRXDec4Back
FRXDec4Front FRXDec4Lv`), logs `logs/S-H4b/`. Nothing committed. Five new modules; no existing module
or statement was edited. `FRX4Prog`/`FRX4Ext` are untouched (A2′ owns them). Handover items 1, 2 and 2′
(Part 25 §6) are done; items 3–6 remain (§6 below).

### 1. Files (`loc.py`: total / code / thm)

| File | loc | Content |
|---|---|---|
| `FRXLagT` (new) | 1,027 / 926 / 30 | Item 1, the target half of `lagIR`: `fwd_blk`, `fwdL_sem`, `fwdLoop_sem` (prefix products `preP` at `pb + t`), `rdF_mk`, `accRow_sem`, `accIR_sem`, `bwd_ptr`, `bwd_mul`, `bwdL_sem`, `bwdLoop_sem` (`acc_c = Σ_t (P_t · sufP (t+1)) · Y_c[t]`), `stRow_sem`, `stAcc_sem`, `rd_zeros`, `tgBody_sem`, `out_ne`, `outC_lt`, `tgIR_sem`, **`lagIR_sem`**, **`lagIR_interp`**; WF/`Writes` helpers; controls `lagIR_node_ctl` (+), `lagIR_row_ctl` (−). |
| `FRXDec4Level` (new) | 115 / 78 / 7 | Item 2, pure: `foldAt4_f₀/f₁`, `mem_consSet4_iff`, `nextMsg4_coords`, `consN4`, `wordN4`, `mem_consN4`, **`level_decode4`**, `msgOf4_embed` (3.x's `FRXLevel` over T4's `CKind` truths). |
| `FRXDec4Back` (new) | 217 / 163 / 9 | Item 2, the back half: `BackLay4` (memory map), **`decBack4IR`** `= scanIR ; lagIR 2^m C c₀ ; bfRowsIR m`, `wf/noLoopT/outs_decBack4IR`, **`cost_decBack4IR`** (exact), `lv4_bounds`, **`decBack4_sem`**; controls `backLay4_m32` (+), `not_backLay4_overlap` (−), `cost_back0_m32`. |
| `FRXDec4Front` (new) | 237 / 198 / 3 | Item 2′: `flagV_consSet4`, `FrontLay4`, **`decFront4IR`** (3.x's front half with every base a parameter), `MsgOk4` (3.x's `MsgOk` at the map's `eb`, `xb`, `yb`, `X`/`Y` of `2^n` entries), `lv4_front`, **`decFront4_sem`**. |
| `FRXDec4Lv` (new) | 102 / 73 / 3 | Items 2 + 2′ composed: **`decLv4IR`**, **`decLv4_sem`**; controls `frontLay4_m32` (+), `not_frontLay4_overlap` (−). |

### 2. What is proved

- **`lagIR_sem`** (`FRXLagT`): on `regs ≤ jb`, `jb + k ≤ pb`, `pb + k ≤ yb`, `yb + 2Ck ≤ ob`,
  `yb + 2Ck ≤ cb`, `ob + 2k(C + 1) ≤ |M|` (one row of slack), `1 ≤ k`, `C ≤ 16`, with `J` listed at `jb`:
  for every target `s < k` and `c < C`, the `F` cell at `ob + 2s + 2kc` is `lagVal J k s y_{c₀+c}`
  (`y_c(j)` the `F` element at `cb + cs·j + 2(c₀ + c)`); the heap outside `[pb, ob + 2kC)` is kept.
  **`lagIR_interp`**: with `J` without repeats below `2^20` and `k = |J|`, that cell is
  `interpF D J y s` (`lagVal_eq`, pass 1).
- **`level_decode4`** (`FRXDec4Level`): 3.x's `level_decode` at every `CKind` (`Snd.T4.msgOf`,
  `consSet`, `decodeL`, `farL`, `mLog`, ladder `CKind.lv`).
- **`decBack4_sem`**: if the flags at `fb` mark `A_c` (`consN4`), the word at `cb + cs·j + 2r` is
  close and `A_c = jointAgree`, then row `c` at `ob + 2kc` holds the `F` values of
  `Snd.T4.msgOf κ L es i (c₀ + c)`, `c < C` (level 0: `c₀ = 4`, `C = 4`; levels 1–4: `c₀ = 0`, `C = 16`).
- **`decFront4_sem`**: the flag at `fb + j` is nonzero iff `j ∈ A_c`, given the basis table, the
  word, P1.i's challenges at `cbS` and a message step meeting `MsgOk4`.
- **`decLv4_sem`**: the two composed on the map `tb < fb < [jb, pb, yl, ob] < eb < xb < yb ≤ cb`.
- **`cost_decBack4IR`**: `(16 + 32n) + (27 + k(1,122 + 72C) + k²(101 + 40C)) + (1 + C(17 + m(741·2^(m−1) + 23))) + 2`,
  `k = 2^m`. **`cost_back0_m32`**: level 0 at `m = 32` (`n = 2^20`, `k = 2^19`, `C = 4`) costs
  **71,758,669,416,262** (`7.18·10^13`), equal to Part 25's model. Levels 1–4 (`C = 16`, from the same
  formula, not yet a theorem): 3.19·10^12, 5.04·10^10, 8.4·10^8, 1.8·10^7.

### 3. Checks (logs in `logs/S-H4b/`)

- **Build.** `lake build FRXDec4Lv FRX4Ext FRSubmission4Cert` green on HEAD `1263569` + the five
  modules: 2,479 jobs (`build8.log`). `FR.lean` imports none of them yet (the orchestrator adds
  them with `nd`).
- **Axioms** (`axioms.log`, 18 declarations: the main theorems and every control): all
  `[propext, Classical.choice, Quot.sound]`.
- **Source rule** (`source-rule.log`): 362 files, 0 findings.
- **Sequential profiles** (`-DElab.async=false`, one core; `prof-*.log`, `prof2-FRXLagT.log`):

  | Module | wall | CPU | note |
  |---|---|---|---|
  | `FRXLagT` | 74.9 s (87 s before a golf of `bwd_ptr`/`tgBody_sem`) | 72.1 s | tactic execution dominates: four `refine`s 6–19 s (the `loopK_run` initial states and `tgBody_sem`'s final tuple); kernel (type checking) ≈ 6 s |
  | `FRXDec4Level` | 7.9 s | 5.2 s | |
  | `FRXDec4Back` | 13.5 s | 10.6 s | type checking 3.2 s |
  | `FRXDec4Front` | 16.1 s | 12.9 s | type checking 3.8 s |
  | `FRXDec4Lv` | 11.3 s | 8.3 s | |

  `FRXLagT` needs a golf before the certificate's build budget sees it (§6, item 6).

### 4. Controls

| Control | Kind | What it shows |
|---|---|---|
| `lagIR_node_ctl` | + | at a listed target `s ∈ J`, `lagIR` outputs row `c₀ + c`'s own value `y(s)` (from `lagIR_interp` + `interpF_self`): the output is the data, not a constant |
| `lagIR_row_ctl` | − | where rows `c₀ + c` and `c₀ + c + 1` differ at `s`, output row `c` is not row `c₀ + c + 1`'s value: the row window is read where stated |
| `backLay4_m32` / `not_backLay4_overlap` | + / − | the back half's map fits at `m = 32`, level 0; an output region on top of `Y` is rejected |
| `frontLay4_m32` / `not_frontLay4_overlap` | + / − | the front half's map fits at `m = 32`, level 0, after the back half's regions (`2^23 + 2^22 + 5·2^20 ≤ 2^25`); `X` on the `eq` table is rejected |
| `cost_back0_m32` | value | the level-0 cost is the model's number |

Pass 1's compiled toy (`probe`, 4 targets × 2 rows against a direct Lagrange interpolation) is now
covered by a theorem (`lagIR_sem`).

### 5. Deviations

1. **Every base is a parameter** (`BackLay4`, `FrontLay4`), as asked: the node's memory map, the
   children's offsets and the segment stride enter only through hypotheses. 3.x's fixed constants
   (`tb0`, `fbF`, `jb0`, `eqB`, `xbM`, `ybM`, `memX`) do not appear in the new statements.
2. **`lagIR_sem` asks for `2k` words of slack after the output** (`ob + 2k(C + 1) ≤ |M|`): `stAcc_sem`'s
   bound is stated at `o + 2kC` with `o = ob + 2s`. Any map with the column store or the `eq` table
   after the output meets it.
3. **The column store must lie above `Y`** (`yb + 2Ck ≤ cb`, pass 1's `yTab_sem`) and above `Y` of the
   front half (`yb + 2n ≤ cb`): the level-0 codeword (`2^27` words at `m = 32`) goes on top of the map.
4. **`MsgOk4`** replaces 3.x's `MsgOk` (the `X`/`Y` region is `2·2^n` words, not `2^19`). The message
   steps (`msgHIR` for levels 0–3, `msgTIR` for level 4) still need their `MsgOk4` lemmas (item 3).

### 6. Handover: what remains, in order

1. **Item 3, the five levels** (`FRXDec4Levels`, new):
   - `msgOk4_lower` / `msgOk4_four`: port `FRXDecLv.msgOk_lower`/`msgOk_four` to `MsgOk4` (their
     programs `msgHIR`/`msgTIR` are parametric; the statements bind `xbM`, `ybM`, `eqB`, `.N30`).
     Level 4's final message is `Snd.T4.finalAt` at `phStart4 47`.
   - The memory map record `Map4 m` (one per `m ∈ {31, 32}`), with `decLv4_sem`'s hypotheses
     discharged by `decide`/`norm_num` (as `backLay4_m32`, `frontLay4_m32`), level 0 with
     `c₀ = 4`, `C = 4`, levels 1–4 with `c₀ = 0`, `C = 16`; levels 1–4 write their rows where level
     `i − 1`'s `msgHIR` reads them.
   - `memX4 = 2^28` (Part 25 F2). The read and the index are parametric in their base except
     `walkPre` (`FRXReadDefs:303`) and the lookup (`FRXLookup:517`, `:689`), which hard-code `memX`:
     add `walkPre4`/`idxIR4` at `memX4`, and the cap offsets at 4.1's positions (`phStart4`, A1′'s
     stride). `ext4With` uses `toProg memX mpwX`: the switch to `memX4` is in `FRX4Prog` (A2′'s
     module; `decBudget` is `fuelBase − 2^27 + …` and becomes `fuelBase − 2^29 + …`).
   - `decLevels4`: an `ite` on the node byte chooses the `m = 31` or `m = 32` map (same program at
     two constant sets), chained as 3.x's `decLevels_sem` (`lvStep_sem`, `lv0Step_sem`).
2. **Item 4, the output `outIR4`**: the `1 + k` children from rows 4–7 of level 0 at `ob0` (stream
   cell `e` is row `4 + e mod 4`, column `e / 4`; with `decBack4_sem` row `c` holds
   `msgOf … (4 + c)`); the signature from the H fields; the aggregate child's segments 2–4 by a
   shifted copy (`(i − 1)·7 mod 8`, or A1′'s new spacer's shift). PACK-4.4 §9.3 (iv): **write
   `reassemble` field by field** (A.3 rows 0–18, row 18 the CapChk field `A`, 61,472 B) so that
   `reassemble_field` is `rfl`; `piSizeOf seq4` is 859,664 after A2′.
3. **Item 5**: `nd := decRead4 ; chain ; decLevels4 ; outIR4`, `DecOk4 nd`, `NodeDec4 nd` (`out` from
   items 3–4), the exact cost and `fuel_covers4`. If A2′ has not landed, write the plug as its own
   module stating what `FRX4Ext` needs.
4. **Item 6**: controls for `Map4` and `outIR4`; golf `FRXLagT` (the four `refine`s of 6–19 s: pass
   register facts as named `have`s before `loopK_run`, as done for `tgBody_sem`'s `hP1 hS1 hJ1`) and
   `FRXLag` (Part 25 §4).

### 7. Open questions

- **Q1.** `lagIR_sem`'s `2k` words of slack (§5.2): acceptable, or should `stAcc_sem` be restated at
  `o + 2k(C − 1) + 2`? It costs nothing in the maps proposed.
- **Q2.** The level-0 map at `m = 32` (`backLay4_m32`, `frontLay4_m32`) uses `[2^20, 2^25 + 2^22]`
  for scratch; the codeword (`2^27` words) then sits at `2^27` and ends at `2^28 = memX4`. That leaves
  no room for the log index above it: the index base moves to `memX4` and `toProg`'s memory must be
  `memX4 + mpw·t` as today. Confirm before item 3 fixes `Map4`.

## Part 27 (track S-H4, pass 3, first step): G2's `local irreducible` in the decoder modules; handover for items 3–6

**Status.** On top of Part 26 (build tree `logs/fr-build-SH4b`, HEAD `1263569` + the S-H4 modules).
The coordinator's answers: Q1 (the `2k` slack) accepted, to be a field of `Map4` with a
non-overlap control; Q2 confirmed with conditions (below). Done in this step: the build-budget
fix only. Items 3–6 are not started; this context is too long to carry them, so §3 is the handover.

### 1. The golf (statements unchanged)

- `attribute [local irreducible] entryK storeM runPrims` after `open` in `FRXLag`, `FRXLagT`,
  `FRXDec4Level`, `FRXDec4Back`, `FRXDec4Front`, `FRXDec4Lv` (G2's fix, `reviews/G2-golf.md`).
- Two base cases closed by `rfl` through `runPrims [] M = M` (`accIR_sem`, `stAcc_sem` at `0`) now
  rewrite with `accIR`/`stAcc`, `semB`, `runPrims_nil`.
- `tgBody_sem`: the `have c3` block's `refine` split into `refine ⟨?_, …⟩` plus `intro`s, the last
  block's memory generalised; `bwd_ptr`: a `runPrims_append` instance instead of `show`.

**CPU, sequential (`-DElab.async=false`), back to back on the shared VM** (load average 20–24; the
"before" file is the same source without the attribute line, `logs/fr-build-SH4b/scratch/noattr/`):

| Module | before | after | change |
|---|---|---|---|
| `FRXLag` | 89.2 s, 100.4 s (two runs) | 53.3 s, 65.4 s | −35 … −40 % |
| `FRXLagT` | 73.6 s (Part 26: 72.1 s at a lower load) | 57.6 s (45.6 s at a lower load, `prof3-FRXLagT.log`) | −22 … −37 % |
| `FRXDec4Level`, `-Back`, `-Front`, `-Lv` | 5.2, 10.6, 12.9, 8.3 s | 5.3, 11.4, 12.9, 6.3 s | unchanged (no loops) |

`FRXLagT`'s remaining hot spot: `tgBody_sem`, 25 s of elaboration, almost all in one step whose
trace (`trace-FRXLagT.log`, `-Dtrace.profiler.threshold=1500`) shows the **ungeneralised** goal
(nested `semXIR … {M := runPrims …}` states) as its expected type: some `generalize` there does not
reach the goal through the `{M := …, o := …}` structure. Next fix: state the five phases of
`tgBody` as separate lemmas (`tgFwd_sem`, `tgZero_sem`, …) on bare memories, so the composite never
holds the nested state.

**Checks after the golf:** `lake build FRXDec4Lv FRX4Ext FRSubmission4Cert` green, 2,479 jobs
(`build9.log`); 18 axiom lines standard (`axioms2.log`); source rule 362 files, 0 findings. loc:
`FRXLag` 923 / 739 / 52, `FRXLagT` 1,038 / 935 / 30.

### 2. The coordinator's conditions on the map (Q2), and what `FRX4Ext` fixes

- `Map4 m` (`m ∈ {31, 32}`) carries, **as kernel-checked literals** (`decide` on numerals only, never
  on a layout computation): non-overlap of every region, `MsgOk4`'s `X`/`Y` regions, the `2k` slack
  after each output, and the fit under `2^28`.
- `toProg mem mpw P` runs on `mem + mpw·t` zero words (`initSt`); the tape (`c`, `|π|`, `π`'s words,
  the log) is **not** in memory: `.input` reads it. So the parse places nothing in memory, and the
  only fixed region is the log index at `[memX, memX + 3t)` (`walkPre`, the lookups). The map must
  stay below `memX4 = 2^28`, with the index at `memX4`.

### 3. Handover for pass 3 (items 3–6, in order; all in new modules, A2′ owns `FRX4Prog`/`FRX4Ext`)

1. **`FRXDec4Msg`**: `msgOk4_lower` (levels 0–3: `msgHIR` from level `i + 1`'s decoded rows, now at
   `ob + 2kc` with `C = 16`) and `msgOk4_four` (level 4: `msgTIR` from π's final field and
   `Snd.T4.finalAt` at `phStart4 47`), ports of `FRXDecLv.msgOk_lower`/`msgOk_four` to `MsgOk4`.
2. **`FRXDec4Map`**: `structure Map4` (fields: `tb`, per level `fb jb pb yl ob eb xb yb cbS cb cs`,
   the index base), `map31`, `map32` as literals; `Map4.ok : BackLay4 … ∧ FrontLay4 … ∧ slack ∧ fit`
   proved by `decide` on the literal record; controls: `map32.ok` (+) and a perturbed record that
   overlaps (−), one for the slack.
3. **`FRXRead4`**: `walkPre4 base`, `idxIR4 base` (the index base a parameter; 3.x hard-codes `memX`
   at `FRXReadDefs:303`, `FRXLookup:517`, `:689`), their `_sem` by re-running 3.x's proofs with
   `base` for `memX`; the cap offsets at 4.1's positions (`phStart4`, A1′'s stride).
4. **`FRXDec4Levels`**: `decLevels4 m` (levels 4 → 0, each `read ; decLv4IR` on `Map4 m`; level 0
   with `c₀ = 4`, `C = 4`), `decLevels4_sem` (port of `FRXNode.decLevels_sem`), and the run-time
   `ite` on the node byte (`N2` → `m = 31`, `N4`/`N8` → `m = 32`); exact `cost_decLevels4`.
5. **`FRXOut4`** (item 4): `reassemble4` **field by field** (A.3 rows 0–18; row 18 = the CapChk field
   `A`, 61,472 B; `piSizeOf seq4 = 859,664`), `reassemble4_field` by `rfl`; `outIR4`: the `1 + k`
   children from rows 4–7 at level 0's `ob` (stream cell `e` = row `4 + e mod 4`, column `e / 4`,
   which is `decBack4_sem`'s row `e mod 4`), the signature from H, the aggregate child's segments
   2–4 by a shifted copy (A1′'s spacer).
6. **`FRXNd4`** (item 5): `nd := decRead4 ; chain ; decLevels4 ; outIR4`, `decOk4_nd : DecOk4 nd`,
   `nodeDec4_nd : NodeDec4 nd`, `cost_nd`, and the statement of what `FRX4Ext` needs.
7. **The patch list for after A2′** (the coordinator schedules it):
   - `FRX4Prog`: `ext4With nd := toProg memX4 mpwX (ext4IRWith nd)` with `memX4 = 2^28`;
   - `FRX4Prog`/`FRXProg`: `decBudget4 t := fuelBase − 2^29 + (fuelPerWord − 16) t` (the prologue
     clears `2^28` words: two steps each), and `fuel_covers4` at `decBudget4`;
   - `FRX4Ext`: `sub4.E := E4X nd S.acc`, `ext := ext4With nd`, `Open4` over `NodeDec4 nd`
     (`FRSubmission4`, `FRSubmission4Cert`).
8. **Item 6**: controls for `Map4`, `outIR4`, `nd`; the `tgBody_sem` split (§1).

## Part 28 (track S-H4, pass 4): the message steps, the memory map `Map4`, the log index and lookup at a parametric base and log position; handover

**Status.** HEAD `632a20f`. Build tree `logs/fr-build-SH4c` (copy of `fr-build-SH4b`, re-snapshotted on
HEAD; `MINE` = `FRXLag FRXLagT FRXDec4Level FRXDec4Back FRXDec4Front FRXDec4Lv FRXDec4Msg FRXDec4Map
FRXRead4`), logs `logs/S-H4c/`. Nothing committed. Three new modules; no existing module was edited.
A2′ has not landed (`A2p-RESULT.md` is a draft), so nothing here uses its worktree edits. Handover
items 1 and 2 (Part 27 §3) are done; item 3 is half done (the index and the lookup, not the read);
items 4–7 are not started (§6).

### 1. Files (`loc.py`: total / code / thm; CPU sequential, `-DElab.async=false`, one module at a time)

| File | loc | CPU (wall) | Content |
|---|---|---|---|
| `FRXDec4Msg` (new) | 177 / 127 / 8 | 8.0 s (11.0 s) | Item 1: `msg4_params`, `msg4_four_params`, `msgH4_next`, **`msgOk4_lower`**, `nextMsg4_four`, **`msgOk4_four`**; controls `msg4_four_ctl`, `msgOk4_empty_neg`. |
| `FRXDec4Map` (new) | 201 / 109 / 16 | 6.1 s (9.0 s) | Item 2: `memX4 = 2^28`, `LvMap`, `LvMap.Ok`, `Map4`, `Map4.Ok`, **`map4`**, **`map4_ok31`**, **`map4_ok32`**, `LvMap.back`/`.front`/`.store`, `lv0_sizes`, `lvU_sizes`, `node_m`, `map4_ok`, `map4_lvU`, `map4_l0`; controls (§4). |
| `FRXRead4` (new) | 1,015 / 873 / 29 | 40.8 s (44.4 s) | Item 3, first half: `walkPre4`, `walkIR4`, `passPre4`, `passIR4`, `sortPre4`, `sortIR4`, **`idxIR4 bX pL`**, `baseX4`; `wf/cost/sizeIR/outs/safe_idxIR4`; `tape_getD_posL4`, `tape_count_le4`, `tape_entry4`, `tape_entries_end4`, `walkLoop4`, `walk_spec4`, `passIR4_sem`, `sortIR4_sem`, **`idxIR4_sorted`**; the lookup `bsBody4`, `foundIR4`, `lookPre4`, **`lookIR4 bX pL`**, `posE4`, `Sorted4`, `tape_answer4`, `ansW_entry4`, `posE_lt4`, `lookup_pure4`, `bsBody4_sem`, `bsLoop4`, `foundIR4_sem`, `lookIR4_sem`, **`idx_lookup4`**. |

Profiles: `logs/S-H4c/prof-*.log`. `FRXRead4`'s cost is that of the 3.x proofs it copies (`FRXLogSpec`,
the sort half of `FRXSortSim`, `FRXLookup`); its hot spots are one `obtain` (5.8 s) and one `refine`
(3.9 s), and `simp` 4.6 s in all (the `simp +decide [ … ]` side conditions, §5.3).

### 2. What is proved

- **`msgOk4_lower`** (levels 0–3, any 4.1 kind): if level `i + 1`'s 16 decoded rows sit at `ob` (row
  `r` at `ob + 2kr`, `k = 2^mLog (i + 1)`: `decLv4_sem`'s output at `c₀ = 0`, `C = 16`) as the `F` values
  of `msgOf (i + 1)`, and `ob + 32k ≤ eb`, `eb + 256 ≤ xb`, `xb + 2n ≤ yb`, then
  `MsgOk4 I (msgHIR n k ob xb yb) s eb xb yb n (mLog i) (nextMsg i)`.
- **`msgOk4_four`** (level 4): `MsgOk4 I (msgTIR n k₄ tw xb yb) …  (nextMsg 4)` given the tape link
  `finalAt es x = (tapeF (tw + 4x), tapeF (tw + 4x + 2))` for `x < k₄`. `k₄ = 2^mLog 4` is 32, 64, 128
  at `m = 30, 31, 32` (`msg4_four_ctl`). The link to π's final field at 4.1's offset belongs where the
  format is fixed (after A2′).
- **`map4_ok31`, `map4_ok32`**: the literal `map4` meets `Map4.Ok` at `m = 31` and `m = 32` (numeral
  inequalities, `decide`). The map:

  | region | base | end at `m = 32` |
  |---|---|---|
  | basis table | `2^20` | `2^20 + 800` |
  | the chain (`chB` … `chEnd`, 3.x's constants) | `2^23` | `2^23 + 6,144` |
  | levels 1–4: flags, `J`, `P`, `Y`, rows, `eq`, `X`, `Y` | `2^24` | `2^24 + 2^23 + 2^20 + 256` |
  | level 0: the same regions | `2^24` | `2^25 + 2^22 + 256` |
  | levels 1–4's word (32 words a position) | `2^26` | `2^26 + 2^23` |
  | level 0's word (128 words a position) | `2^27` | `2^28` |
  | the log index | `memX4 = 2^28` | `2^28 + 2|L|` |

  Levels 1–4 run before level 0 and share one map (3.x's `obL` design). `Map4.Ok` asks, besides each
  level's order and `2k` slack, that levels 1–4 keep level 0's word, that level 1's rows (read by
  level 0's message step) lie below level 0's `eq` table, and that level 0's word ends at the index.
  `map4_lvU`/`map4_l0` restate it at a node kind's `2^logN`, `2^mLog`; `LvMap.back`/`LvMap.front` give
  `BackLay4`, `FrontLay4` and `decLv4_sem`'s `hoe`.
- **`idxIR4_sorted`** (3.x's `idxIR_sorted` with `memX ↦ bX`, `posL ↦ pL`): on a tape with
  `5 + ⌈|π|/8⌉ = pL`, `regs ≤ bX ≤ 2^60`, `pL ≤ 2^60`, after `idxIR4 bX pL` the cells `bX + a`,
  `a < |L|`, hold exactly the tape positions `pL + 1 + entryOff L k`, strictly sorted by the key.
  **`idx_lookup4`**: `lookIR4 bX pL` finds the first entry with answer `t` (`FRLog.ansIdx`), or sets
  `rFd = 0`, and keeps the index sorted. `cost_idxIR4 = 2592 + ⌊t/5⌋·11871` (3.x's), `safe_idxIR4`.

### 3. Checks (logs in `logs/S-H4c/`)

- **Build.** `lake build FRXRead4 FRXDec4Map FRXLagT FR Solution` green on HEAD + the S-H4 modules:
  2,590 jobs (`build-final.log`). `FR.lean` imports none of the S-H4 modules (the orchestrator adds them
  with `nd`).
- **Axioms** (`axioms.log`, 25 declarations: the main theorems and every control): all within
  `propext`, `Classical.choice`, `Quot.sound`.
- **Source rule** (`source-rule.log`): 365 files, 0 findings.

### 4. Controls

| Control | Kind | What it shows |
|---|---|---|
| `msgOk4_empty_neg` | − | `MsgOk4` is not trivial: the empty step does not lay out a nonzero message over a zero `X` row |
| `msg4_four_ctl` | value | the final message's sizes per `m` (32, 64, 128) |
| `map4_ok31`, `map4_ok32` | + | the map fits both node sizes |
| `map4_ctl` | value | the bases are the table's powers of two; `ix = memX4` |
| `not_map4_overlap` | − | level 0's `X` on its `eq` table is rejected |
| `not_map4_slack` | − | level 0's `eq` table at `ob + 2kC` (no `2k` slack) is rejected |
| `not_map4_fit` | − | level 0's word one position higher (into the index) is rejected |
| `not_map4_rows` | − | level 1's rows above level 0's `eq` table are rejected |

`idxIR4_sorted`/`idx_lookup4` are 3.x's theorems at parameters; their controls are 3.x's (`baseX4_ctl`,
and 3.x's `FRXLookup`/`FRXSortSim` controls at `bX = memX`, `pL = posL`).

### 5. Deviations and findings

1. **`posL` is hard-coded too (finding).** Part 26/27 said only the index base needed a parameter. Every
   index, lookup and read program also reads `|L|` at tape word `posL = 5 + 99,738`, which is 3.x's
   `piSize/8`: `walkPre`, `passPre`, `sortPre`, `lookIR` (so `getIR` and the whole ladder read), and the
   chain (`FRXChain`, `FRXChainTop`: 21 uses). A 4.1 node proof has `|π| = piSizeOf seq4` (798,192 at
   HEAD, 859,664 after A2′). So the 4.1 versions take the log's position `pL` as a parameter, with
   `hs : 5 + (|π| + 7)/8 = pL`; the node branch instantiates `pL = 5 + piSizeOf seq4 / 8` once A2′ fixes
   it. This also makes them independent of A2′'s numbers.
2. **One map for `m = 31` and `m = 32`** (`map4`), not two records: both fit, and the memory is `2^28`
   either way. `decLevels4`'s run-time `ite` still chooses between the two ladders (their constants
   differ); the map does not.
3. **`simp +decide [ … ]` instead of `simp +decide only [ … ]`** in `FRXRead4`'s side conditions: with a
   variable constant word (`BitVec.ofNat 64 pL`) `decide` cannot close `WF`/`Lo`, and the `only` set
   leaves `Prim.dst`'s `match` unreduced. It costs a few seconds (§1); a golf can restore `only` lists
   with `Prim.dst`'s equation lemmas.
4. **The chain stays at 3.x's constants** (`chB = 2^23`, `ansB`, `chEnd`) in `map4`: the chain's region
   is between the basis table and the levels. If the 4.1 chain moves, `Map4.Ok`'s two chain conjuncts
   move with it.

### 6. Handover: what remains, in order

1. **Item 3, second half: the ladder read at 4.1** (`FRXRead4b`, new; or append to `FRXRead4`).
   - Port `FRXRead`'s `getIR`, `nodeBody`, `colIR`, `posBody`, `readIR` and their semantics
     (`getIR_sem`, `nodeBody_sem`, `nodeLoop`, `colIR_sem`, `posBody_sem`, `posLoop`, **`readIR_sem`**,
     **`read_spec`**, `read_spec_F`, `readIR_frame`), about 1,200 lines, on `lookIR4 bX pL`, `Sorted4`,
     `posE4` (this pass's), by the same mechanical method (journal 77; the extraction and rename scripts are in
     `logs/S-H4c/port-tools/`: `ext.py` cuts declarations out of a 3.x module, `port.py` renames).
   - The cap offsets at 4.1 (`capOff`, `capW0`, `capOffL`, `capWL`, `capLogL`, `tape_cap`,
     `tape_capL`): from `fieldOff`/`phStart4` at `seq4`, as parameters with their values checked after
     A2′. `readLv4 i` at `map4.lU.cb`, `nw = 32`; `read04` at `map4.l0.cb`, `nw = 128`, `np = 2^(m − 12)`.
   - The read's store must stay below the index: `cb + nw·np ≤ bX` (`map4_ok`'s fit gives it).
2. **The chain at `seq4`**: `chainIR nRep chTab seedIR` reads `posL` (21 uses in `FRXChainTop`) and its
   table is built from 3.x's `phStart`. Port with `pL` and `phStart4`; `cbS4 i = ansB + 4(phStart4
   (26 + 5i) + 1)`, and prove `cbS4 i + 8ℓ + 4 ≤ chEnd ≤ map4.l0.fb` (for `LvMap.front`).
3. **Item 4, `FRXDec4Levels`**: `decLevels4 m` (levels 4 → 1 on `map4.lU`, then level 0 on `map4.l0`
   with `c₀ = 4`, `C = 4`), each `read ; decLv4IR` with `msgOk4_lower`/`msgOk4_four`; `decLevels4_sem`
   (3.x's `decLevels_sem`); the `ite` on the node byte; the exact cost.
4. **Item 5, `FRXOut4`**: as Part 27 §3 item 5 (`reassemble4` field by field, A.3 rows 0–18, row 18 =
   `A`; `outIR4`).
5. **Item 6, `FRXNd4`**: `nd4 := idxIR4 memX4 pL4 ; read04 ; chain4 ; decLevels4 ; outIR4`,
   `decOk4_nd4`, `nodeDec4_nd4`, `cost_nd4`, with `pL4 = 5 + piSizeOf seq4 / 8`.
6. **Item 7**: controls for `outIR4`, `nd4`; the `tgBody_sem` split in `FRXLagT` (Part 27 §1: one lemma per
   phase on a bare memory; 25 s to remove).

### 7. The patch list for after A2′ (exact; for the orchestrator to schedule; not applied)

`FRX4Prog.lean` (A2′'s):

```diff
+/-- The node decoder's memory below the log index (S-H4, Part 25 F2; `FRXDec4Map`): `2^28` words. -/
+def memX4 : ℕ := 2 ^ 28
+
+/-- What the node branch may cost at `memX4`: `decBudget` less the extra `2^28` words cleared. -/
+def decBudget4 (t : ℕ) : ℕ := fuelBase - 2 ^ 29 + (fuelPerWord - 16) * t
@@ structure DecOk4
-  cost : ∀ t, cost nd t ≤ decBudget t
+  cost : ∀ t, cost nd t ≤ decBudget4 t
@@
-def ext4With (nd : XIR) : XProg := toProg memX mpwX (ext4IRWith nd)
+def ext4With (nd : XIR) : XProg := toProg memX4 mpwX (ext4IRWith nd)
@@ theorem decOk4_ndNone
-  cost := fun t => by simp [ndNone, cost, blkSteps, decBudget, fuelBase, fuelPerWord]; omega
+  cost := fun t => by simp [ndNone, cost, blkSteps, decBudget4, fuelBase, fuelPerWord]; omega
@@
-theorem fuel_covers4 {nd : XIR} (h : ∀ t, cost nd t ≤ decBudget t) (t : ℕ) :
-    memX + mpwX * t + cost (ext4IRWith nd) t + 8 ≤ fuel t := by
+theorem fuel_covers4 {nd : XIR} (h : ∀ t, cost nd t ≤ decBudget4 t) (t : ℕ) :
+    memX4 + mpwX * t + cost (ext4IRWith nd) t + 8 ≤ fuel t := by
   have := h t
   have := cost_ext4IRWith nd t
-  simp only [memX, mpwX, fuel, fuelBase, fuelPerWord, decBudget] at *
+  simp only [memX4, mpwX, fuel, fuelBase, fuelPerWord, decBudget4] at *
   omega
```

Then `FRXDec4Map`'s own `def memX4` is deleted and `FRXDec4Map` uses `X4.memX4` (one definition).

`FRX4Ext.lean` (A2′'s): every `memX` that is the program's memory becomes `memX4` (lines 259, 262,
271, 299–300, 329, 335, 347, 368, 415, 459, 569–576, 609 at HEAD: `initSt (memX + mpwX * …)`,
`den memX mpwX`, `Eden memX mpwX`, and the side conditions `by simp only [regs, memX]; norm_num` →
`[regs, memX4]`).

`FRSubmission4.lean`, `FRSubmission4Cert.lean`, once `FRXNd4` exists:

```diff
-  ext := X.X4.ext4With X.X4.ndNone
+  ext := X.X4.ext4With X.nd4
-def sub4 : Submission := { sub0 with E := X.X4.E4X X.X4.ndNone sub0.acc }
+def sub4 : Submission := { sub0 with E := X.X4.E4X X.nd4 sub0.acc }
@@ structure Open4
-  resid : ∃ D : NodeDec4 ndNone, ∀ vk, Snd.R4.Resid4H (Impl.finC finPf) Layout.lRows 0 sub4 ndNone D vk
+  resid : ∃ D : NodeDec4 X.nd4, ∀ vk, Snd.R4.Resid4H (Impl.finC finPf) Layout.lRows 0 sub4 X.nd4 D vk
@@ theorem certificate_sub4
-    sub4_ext sub4_fuel decOk4_ndNone D hR complete_rev4 delta_rev4
+    sub4_ext sub4_fuel X.decOk4_nd4 D hR complete_rev4 delta_rev4
```

and `Open4`'s `D` is then discharged by `X.nodeDec4_nd4` (item 6), which removes `resid`'s `∃ D`.

### 8. Open questions

- **Q1.** The chain: keep 3.x's constants (`chB = 2^23`, 512 answer slots; 4.1's P1 positions are below
  `phStart4 46 + 1 ≤ 449`, to be checked) and port only `pL` and the table, or move it? `map4` assumes
  the former.
- **Q2.** `FRXRead4` copies about 870 code lines of 3.x proofs (40.8 CPU-s). Once the 3.x decoder leaves
  the certificate's closure (retirement plan step 2), the 3.x modules can go; until then the build pays
  for both. Should the orchestrator schedule the retirement before item 6, so that the build budget sees
  only one copy?

## Part 29 (track S-H4, pass 5): one copy of the index, the lookup, the read and the chain, parametric in the index base and the log's position; FRXRead4 deleted; handover

**Status.** Started at HEAD `6d79280`; re-snapshotted on `4d5700c` (G3 committed at `302b523`). Build tree
`logs/fr-build-SH4d` (copy of `fr-build-SH4c`; `MINE` = the S-H4 modules + `FRXLogSpec FRXSortSim
FRXLookup FRXReadDefs FRXRead FRXReadLv FRXChain FRXChainSem FRXChainLoop FRXChainTop FRXChainFlock
FRXDec FRXLog FRXNode FRXOutRun`), logs `logs/S-H4d/`, tools `logs/S-H4d/tools/` (`blk.py` splits a module
into declarations, `fold1.py` … `fold4.py` are this pass's edits as scripts). Nothing committed. The
orchestrator's Q2 ruling (generalise in place, one copy of each proof) is done for the index, the lookup,
the ladder read, the read's frame and the chain's count/start/scan. Items 1–4 of the handover
(`FRXDec4Levels`, `FRXOut4`, `FRXNd4`, the controls and the `tgBody_sem` split) are **not started**
(§5). `nd` does not exist yet; `Open4` still holds `∃ D : NodeDec4 ndNone`; the entry stays PROVISIONAL.

### 1. What changed, file by file (`loc.py`; code lines before → after)

| File | code | What |
|---|---|---|
| `FRXLogSpec` | 215 → 262 | The walk at parameters: `walkPre4 bX pL`, `walkIR4`, `wf_walkIR4`, `tape_getD_posL4`, `tape_count_le4`, `tape_entry4`, `tape_entries_end4`, `walkLoop4`, **`walk_spec4`** (moved from `FRXRead4`). 3.x's `tape_entry`, `tape_entries_end`, `walk_spec` are one-line instances at `memX`, `posL`; `hs_posL : π.size = piSize → 5 + (|π| + 7)/8 = posL`; `walkIR_eq : walkIR = walkIR4 memX posL` (`rfl`). 3.x's `walkLoop` (internal) is gone. |
| `FRXSortSim` | 690 → 749 | `passPre4`/`passIR4`/`sortPre4`/`sortIR4`/`idxIR4`/`baseX4`, `wf/cost/sizeIR/outs/safe_idxIR4`, `passIR4_sem`, `sortIR4_sem`, **`idxIR4_sorted`**. 3.x's `idxIR_sorted` is an instance; `idxIR_eq` (`rfl`). 3.x's internal `passIR_sem`, `sortIR_sem`, `baseX*` are gone. |
| `FRXLookup` | 771 → 847 | `bsBody4`, `foundIR4`, `lookIR4`, `lookPre4`, `posE4`, `Sorted4`, `tape_answer4`, `ansW_entry4`, `posE_lt4`, `lookup_pure4`, `bsBody4_sem`, `bsLoop4`, `foundIR4_sem`, **`lookIR4_sem`**, **`idx_lookup4`**. 3.x: `posE := posE4 posL`, `Sorted := Sorted4 posL` (`abbrev`s, so `⟨r1, r2, r3⟩` in `FRXNode` still elaborates); `tape_answer`, `ansW_entry`, `posE_lt`, `lookup_pure`, `lookIR_sem`, `idx_lookup` are instances; `lookIR_eq4` (`rfl`). |
| `FRXReadDefs` | 327 → 353 | `getIR bX`, `nodeBody bX pL i`, `colIR bX pL i` (in place: no 3.x caller), `posBody4 bX pL …`, `readIR4 bX pL …`; 3.x `posBody := posBody4 memX posL`, `readIR` keeps its literal body (so `FRXNode`'s `rw [readIR, semXIR_seq]` is unchanged), `readIR_eq` (`rfl`). `tape_query4` (+ 3.x instance), `wf_lookIR4`, `lookIR4_nw`, `wf/noLoopT/outs_readIR4` (+ 3.x instances), `cost_lookIR4`, **`cost_readIR4`** (`14 + np(6,576 + 6,544 sib + 25 nw)`, any constants). |
| `FRXRead` | 1,169 → 1,201 | `Dom4 pL` (`hs : 5 + (|π| + 7)/8 = pL`), `Dom.d4 : Dom → Dom4 posL`; every index-dependent lemma at `bX`, `pL` in `section Read4` (`Dom4.small`, `tp_posL4`, `look_spec`, `getIR_sem`, `nodeBody_sem`, `nodeWalk`, `nodeLoop`, `colIR_sem`, `posBody_sem`, **`posLoop4`**, **`readIR4_sem`**, **`readIR4_frame`** (moved from `FRXNode`)); 3.x's `posLoop`, `readIR_sem` are instances; `read_spec`, `read_spec_F` unchanged. |
| `FRXReadLv` | 108 → 101 | `cost_readIR` is `cost_readIR4 memX posL`. |
| `FRXChain` | 164 → 164 | In place: `cntIR pL`, `startPs pL`, `chainIR pL N tab sd`, `wf_cntIR pL`, `wf/cost/sizeIR/outs_chainIR pL …`. |
| `FRXChainTop` | 318 → 318 | `cnt_sem`, `chainIR_sem` with `{pL}` and `hs : 5 + (|π| + 7)/8 = pL`; `cnt_heap`, `cnt_regs`, `startPs_vals`, `startPs_frame` take `pL`. |
| `FRXChainLoop` | 688 → 688 | `entriesAt_tape` at `pL`. |
| `FRXChainFlock`, `FRXDec`, `FRXNode` | 182, 105, 687 (unchanged counts) | The 3.x callers: `chainIR posL nRep …`, `hs_posL hs`; `safe_cntIR pL (hp : pL < 2^64)`, `wordsOf_le`, `safe_chainIR` at `pL`; `FRXNode.readIR_frame` is `readIR4_frame` at `memX`, `posL`. |
| `FRXRead4` | 873 → **deleted** | Everything it held now lives once, in the modules above. |
| **Total** (13 files) | **6,297 → 5,657** (−640) | |

No 3.x statement changed apart from the added parameter (`chainIR posL …`, `cntIR posL`, the chain
theorems' `hs` in `pL` form: 3.x callers pass `hs_posL hs`). Every instance is a term proof
`X4 (bX := memX) (pL := posL) (by decide) (by decide) (by decide) …` of the parametric theorem.
`FRXLog`'s 3.x programs (`walkIR`, `sortIR`, `lookIR`, `idxIR`) stay (G3's module at the time; four
small definitions) and are `rfl`-equal to the parametric ones (`walkIR_eq`, `idxIR_eq`, `lookIR_eq4`).

### 2. CPU, before and after (sequential `-DElab.async=false`, one module at a time; logs `logs/S-H4d/cpu-*.txt`, `prof-*.log`)

Before = HEAD `6d79280` in `fr-build-SH4c`, after = this pass in `fr-build-SH4d`, run side by side (two
processes, load ≈ 20–30):

| Module | before | after |
|---|---|---|
| `FRXLogSpec` | 14.6 | 15.7 |
| `FRXSortSim` | 28.7 | 33.7 |
| `FRXLookup` | 25.3 | 27.9 |
| `FRXReadDefs` | 20.8 | 19.2 |
| `FRXRead` | 33.4 | 35.6 |
| `FRXReadLv` | 11.8 | 12.2 |
| `FRXRead4` | 44.6 (`prof-before-FRXRead4.log`) | — |
| **total** | **179.2** | **144.3** (−35 CPU-s, −20 %) |

`FR`'s closure did not import `FRXRead4`, so `FR` alone pays +9.7 CPU-s (the parametric proofs carry a
few more hypotheses); the 4.1 node decoder, which needs these theorems at `memX4`, now adds nothing for
them (it would have added 44.6). Later, at a lower load (`cpu-after2.txt`, `prof-after2-*.log`):
`FRXRead` 24.1 (with `readIR4_frame`), `FRXChain` 10.4, `FRXChainTop` 10.8, `FRXDec` 7.7, `FRXNode`
22.2 (without its copy of the frame proof). The chain's edits are a parameter only; not A/B-measured.

### 3. Checks

- **Build.** `lake build FR Solution FRXDec4Lv FRXDec4Map FRXLagT FRXChainFlock FRXDec FRXNode` green on
  HEAD `4d5700c` + this pass: 2,589 jobs (`logs/S-H4d/build2.log`, 8 min 24 s wall); then `FRXNode
  FRXReadLv` after `readIR4_frame` (2,279 jobs).
- **Axioms** (`logs/S-H4d/axioms.log`, `logs/fr-build-SH4d/ax/AxSH4d.lean`, 20 declarations: the
  parametric theorems and their 3.x instances, `read_spec`, `chain_spec`, `decLevels_sem`): all within
  `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- **Source rule** (`logs/S-H4d/source-rule.log`): 364 files, 0 findings.
- **Controls.** No new definition the certificate relies on: the parametric programs are the old ones
  with two constants abstracted, and their 3.x instances are `rfl` (`walkIR_eq`, `idxIR_eq`, `lookIR_eq4`,
  `readIR_eq`); the 3.x controls (`baseX4_ctl`, `bsRun_ctl`, `nodeStepP_toy*`, `colWord_toy*`, `fsMsgs_*`)
  still check them at `memX`, `posL`.

### 4. Deviations and findings

1. **Names.** Where a 3.x module outside my reach used a theorem with its old signature (`FRXNode`,
   `FRXChainLoop`, `FRXDec`, `FRXNodeRun` at the start of this pass, G3's), the parametric theorem has a
   `4` name and the old name is its instance. Where no outside module used a lemma (`getIR`, `nodeBody`,
   `colIR`, `look_spec`, `nodeBody_sem`, `colIR_sem`, …; the chain's `cntIR`, `startPs`, `chainIR`) it is
   generalised in place under its own name.
2. **`FRXLog` not edited.** G3 held it when this pass started. Its four 3.x programs remain beside the
   parametric ones (equal by `rfl`); folding them is a few lines once someone next edits `FRXLog`.
3. **`simp +decide only` → `simp +decide`** on `WF`/`Lo` side conditions where a constant word is now a
   variable (`toWord bX`, `toWord (pL + 1)`): as pass 4's journal 77.
4. **Lines over 100 columns**: 132 in the 11 edited modules (95 before, 32 of them in `FRXRead4`), from the
   mechanical rename. A reflow is a golf item; the source rule does not check it.
5. **The chain at revision 4.1 is not done.** `chainIR` now takes `pL`, but its table (`chTab`,
   `fsMsgs`, `nRep`, `tabW_chTab`, `chain_spec`) is 3.x's transcript (`FRXChainFlock`). The 4.1 table comes
   from `seq4`'s Fiat–Shamir positions, which A2′ is changing (`FRTranscriptDefs`, `FRShape4`); it is the
   first item after A2′ lands (§5).

### 5. Handover: what remains, in order

1. **`FRXDec4Levels`** (new). `readLv4 i := readIR4 memX4 pL i (cw i) map4.lU.cb 32 (sib i) (2^logN i)`
   with the 4.1 cap words `cw`, heights `sib` as parameters (their values from `FRShape4` after A2′);
   `stepU4`, `lvStep4_sem` (port of `FRXNode.lvStep_sem`: `readIR4_sem` + `readIR4_frame` + `decLv4_sem` +
   `msgOk4_lower`/`msgOk4_four`, on `map4.lU`, with `KeepR4` = below `lU.fb`, the chain's
   `[chB, chEnd)`, from `map4.l0.cb` on); `lv0Step4_sem` on `map4.l0` (`c₀ = 4`, `C = 4`);
   `decLevels4`, **`decLevels4_sem`** (port of `decLevels_sem`); the `ite` on the node byte (`m = 31`/`32`
   share `map4`; only the ladder constants differ); exact `cost_decLevels4` (`cost_readIR4`,
   `cost_decBack4IR`). The P1 challenges' positions `cbS4 i` come from the 4.1 chain (item 2): state them
   as a hypothesis `hS` (as `decLv4_sem` does) until then.
2. **The 4.1 chain table** (after A2′): `fsMsgs4`/`nRep4`/`chTab4` from `seq4`'s FS positions,
   `tabW_chTab4`, `chain_spec4` (port of `FRXChainFlock`, with `chainIR pL4` and `hs` at `pL4 = 5 + piSizeOf
   seq4 / 8`); `cbS4 i = ansB + 4(phStart4 (26 + 5i) + 1)` and `cbS4 i + 8ℓ + 4 ≤ chEnd ≤ map4.l0.fb`
   (`LvMap.front`). Check `nRep4 < 2^9` (`chainIR_sem`'s `hN`) and that the answers fit `[ansB, chEnd)`.
3. **`FRXOut4`**: `reassemble4` field by field (A.3 rows 0–18, row 18 the CapChk field `A`;
   `reassemble4_field` by `rfl`), with **row 18's size a parameter or computed from `aBytes`**, so that one
   module serves both branches: A2′ (on `v4/rev44`, worktree `recursion.fast-submissions-rev44`) found a
   cap of 1,408 entries, so `A` is 1,408·32 + 32 = **45,088 B** and `piSizeOf seq4 = 843,280` there; main
   keeps the current format (798,192). `outIR4` from level 0's rows 4–7 at `map4.l0.ob`.
4. **`FRXNd4`**: `nd4 := idxIR4 memX4 pL4 ; readIR4 memX4 pL4 0 … ; chainIR pL4 nRep4 chTab4 seedIR4 ;
   decLevels4 ; outIR4`, `decOk4_nd4` (`safe_idxIR4`, `safe_chainIR`, `noLoopT_readIR4`, `cost_*`),
   `nodeDec4_nd4`, `cost_nd4`.
5. Controls for `outIR4`, `nd4`; the `tgBody_sem` split in `FRXLagT` (Part 27 §1); the line reflow
   (§4.4).

### 6. The patch list for after A2′ (applies on `v4/rev44`, not on main)

A2′ landed on the separate branch `v4/rev44`; on main `FRX4Prog`/`FRX4Ext` keep 798,192 and are not
edited. Part 28 §7's list (`memX4`, `decBudget4`, `ext4With nd`, `sub4.E`, `Open4` over `NodeDec4 nd4`)
applies on rev44, where `pL4 = 5 + 843,280 / 8 = 105,415`. Two updates: `FRXDec4Map`'s `memX4` is still the only definition of
`memX4` (delete it there once `FRX4Prog` has it), and the read/index at 4.1 are now `readIR4 memX4 pL4 …`,
`idxIR4 memX4 pL4` in the existing modules (no `FRXRead4`).

### 7. Open questions

- **Q1.** `FRXLog`'s four 3.x programs: fold them now (`def walkIR := walkIR4 memX posL` needs the
  parametric definitions moved into `FRXLog`, a G3-golfed module), or leave them until the 3.x decoder
  retires (retirement step 2)? They cost nothing measurable.

## Part 30 (track S-H4, pass 6): the five levels at a node kind, the 4.1 chain table, the node branch's decode; `memX4` in the program; handover

**Status.** HEAD `cb12cc4` (`a84753a` + a QUEUE commit). Build tree `logs/fr-build-SH4e` (copy of
`fr-build-SH4d`, `snap.sh` on HEAD; `MINE` = `FRXDec4Levels FRXDec4Map FRXSeed FRXChain4 FRXDec4F0 FRXProg
FRX4Prog FRX4Ext`), logs `logs/S-H4e/`. Nothing committed. Handover items 1 and 2 (Part 29 §5) are done;
item 4's decode half is done (`decF04`, its semantics, loop bounds and cost) and item 5's memory half
(`memX4`, `decBudget4`, `ext4With` at `memX4`) is applied on main. **Not done: item 3 (`FRXOut4`: the 4.1
proof decoder and the output program), hence `nd`, `NodeDec4 nd` and the plug of `nd` into
`FRSubmission4*`.** `Open4` still holds `∃ D : NodeDec4 ndNone`; the entry stays PROVISIONAL. §6 is the
handover.

### 1. Files (`loc.py`: total / code / thm; CPU sequential, `-DElab.async=false`, one module at a time; `logs/S-H4e/cpu-*.txt`, `prof-*.log`)

| File | loc | CPU (wall) | Content |
|---|---|---|---|
| `FRXDec4Levels` (new) | 677 / 507 / 35 | 22.1 s (22.0 s); kernel 5.3 s | Item 1. `readK4`, **`readK4_sem`**, `rdF_colWord`, `lv4_read`; the programs `msgT4`, `msgU4`, `msg04`, `decU4`, `dec04`, `stepU4`, **`decLevels4 κ pL cw cbS tw`**, `decLevels4_m`; `KeepR4`, `lvU4_nums`, `lv04_nums`, `map4_nums`, `eqt4_keep`, **`lvStep4_sem`**, `msgT4_ok`, `msgU4_ok`, `msg04_ok`, **`lv0Step4_sem`**, **`decLevels4_sem`**; `wf_setA4`, `wf/noLoopT/outs_decLv4IR`, **`cost_decLv4IR`**, `wf/noLoopT/outs/cost_readK4`, `wf/noLoopT/outs_decLevels4`, `cost_stepU4`, `cost_dec04`, `cost_decLevels4_eq`, `cost_msgT4`, `cost_msgU4`, **`cost_decLevels4`**; controls (§4). |
| `FRXChain4` (new) | 289 / 187 / 22 | 28.9 s (28.7 s); kernel ≈ 15 s | Item 2, parametric in the item sequence `S`: `phaseMsgs4`, `fsMsgs4`, `msgOkB`, `fsMsgs4_zero`, `fsQ4`, `fsQ4_zero`, `stateIn_fsQ4`, `tabEnt4`, `chTab4`, `chTab4_length`, `chTab4_getD`, `msgOkB_of`, **`tabW_chTab4`**, `seedQ_size`, **`chain_spec4`**, **`chain_dec4`**; at `seq4`: `fsMsgs4_length`, `msgItem4`, **`fsMsgs4_items`**, **`fsMsgs4_aligned`**, `nRep4 = 456`, `nRep4_ctl`, `cbS4`, **`sAt4_words`**, `cbS4_bounds`; controls. |
| `FRXDec4F0` (new) | 393 / 273 / 19 | 20.2 s (20.0 s) | Items 1 + 2 composed (item 4's decode half): main's format `pL4`, `capFO4`, `capPi4`, `cw4`, `finFO4`, `finPi4`, `tw4`, `fmt4_vals`, **`fmt4_ctl`**, `lv_cap4`, `tape_cap4`, `tapeF_fin4`; the node-byte dispatch `rF2`, `rF4`, `kindNd4`, `wf/lo_kindNd4`, **`kindNd4_sem`**, `pickNd`, `ndK4`, **`ndK4_sem`**; **`decF04 κ`**, **`decF04_sem`**, `wf_seedIR4`, `wf/outs_decF04`, **`safe_decF04`**, `cost_decF04_eq`, **`cost_le_decF04`**; controls. |
| `FRXSeed` (edited) | 425 / 316 / 37 → 440 / 323 / 40 | 16.8 s | In place over `48 ≤ |π|` (§3): `seedPay_length`, `tape_seed`; new `seedVal_eq4`, `fsQ_zero`, **`seedOK_seedIR4`**; 3.x's `seedVal_eq`, `seedOK_seedIR` are now instances. |
| `FRXProg` (edited) | 208 / 112 / 8 → 219 / 115 / 9 | 11.5 s | Item 5: `memX4 := 268435456` (`memX4_eq : memX4 = 2^28`), `decBudget4 t := fuelBase − 2^29 + (fuelPerWord − 16) t`. |
| `FRX4Prog` (edited) | 278 / 169 / 26 → 279 / 169 / 26 | 12.4 s | Item 5 (§3): `DecOk4.cost` at `decBudget4`, `ext4With` at `memX4`, `fuel_covers4` at `memX4`/`decBudget4`. |
| `FRX4Ext` (edited) | 742 / 543 / 61 (unchanged) | 14.1 s | Item 5 (§3): every `memX` of the program's memory is `memX4` (21 occurrences). |
| `FRXDec4Map` (edited) | 201 / 109 / 16 → 201 / 108 / 16 | 9.1 s | `memX4` moved to `FRXProg`; `map4` is an `abbrev` (§5.1). |

New code: 967 lines (3 modules); edited modules +11 code lines. The three new modules cost 71.2 CPU-s
sequentially; they are not yet in the certificate's closure (`FR`/`FRSubmission4` import none of them).

### 2. What is proved

- **`readK4_sem`**: on a domain tape (`Dom4 pL`) with the sorted index at `memX4`, if the tape holds the
  cap `T4.capDig es i` at tape word `cw` (`hcap`), `readK4 pL κ i cw sb nw` leaves at `sb + nw·j + 2r`
  the committed word `T4.wordOf κ L es i r j` (`2·rows ≤ nw`), keeps the index, keeps the heap outside
  `[sb, sb + nw·2^logN)`. The height is the kind's ladder (`(CKind.lv κ i).sib`).
- **`decLevels4_sem`** (3.x's `decLevels_sem` on `map4`, any node kind `κ`): given level 0's word at
  `map4.l0.cb` (128 words a position), the cap links at `cw i` (`i = 1 … 4`), the P1 challenges'
  words `rdK (cbS i + 8v) = T4.sAt es i v` with `cbS i` above the basis table and below the levels'
  regions, the final message's link `T4.finalAt es x = (tapeF (tw + 4x), tapeF (tw + 4x + 2))`, and at
  every level `¬ farL` and `A_c = jointAgree`: **level 0's rows `4 … 7` sit at
  `map4.l0.ob + 2^(mLog 0 + 1) q + 2x` as the `F` values of `T4.msgOf κ L es 0 (4 + q)`**. Levels 4 … 1
  decode all 16 rows into `map4.lU.ob` (`lvStep4_sem`), level `i + 1`'s rows being level `i`'s message
  (`msgU4_ok`, `msg04_ok`); level 4's message is the tape's (`msgT4_ok`).
- **`cost_decLevels4`** (exact): `18,780,858,425,058` (`2^44.1`) at `N2`, `75,054,361,432,716` (`2^46.1`)
  at `N4`/`N8` — `logs/S-H4/fuel-check4.py`'s model to the step (level 0: `1.80·10^13`, `7.18·10^13`).
- **`chain_spec4`** (any item sequence `S`, any `N < 2^9`): on a domain tape of a proof inside which
  `S`'s messages lie 8-byte aligned (`hA`, a decided check), with no state hit in the log, the answer at
  `ansB + 4p` (`p < N`) is the first-match chain's `fmAns (fsQ4 S vk c π) st₀ L p`, and the chain keeps
  the heap outside `[chB, chEnd)`. **`chain_dec4`**: the same for `seedIR` with `vk = vkOf π`.
  At `seq4`: **`fsMsgs4_items`** (the targets' kinds and lengths are `T4.fsItems4`, 482 positions),
  **`fsMsgs4_aligned`**, `nRep4 = 456` (`nRep4_ctl`: P1.0 … P1.4 start at 332, 375, 402, 426, 448; the final
  absorb is at 456), **`sAt4_words`** (`cbS4 i = ansB + 4(phStart4 (26 + 5i) + 1)` holds `T4.sAt es i`),
  `cbS4_bounds` (`2^20 + 800 ≤ cbS4 i`, `cbS4 i + 8ℓ + 4 ≤ chEnd ≤ map4.lU.fb`).
- **`decF04_sem`** (3.x's `decF0_sem` at a 4.1 node kind, main's format): on a domain tape of a proof of
  `piSizeOf seq4` bytes whose log has no state hit, if `fmAns (fsQ4 seq4 (vkOf π) c π) st₀ L p =
  some (ansAt es p)` for `p < nRep4`, `T4.capDig es i e = capPi4 i π e` (`i < 5`), `T4.finalAt es x =
  finPi4 π x`, and every level is close with `A_c = jointAgree`, then after `decF04 κ` the rows `4 … 7`
  of `f⁽⁰⁾` sit at `map4.l0.ob` (as above). These are 3.x's `E_node` hypotheses at revision 4.1: they are
  the `Links` the eventual `NodeDec4 nd` will carry.
- **`ndK4_sem`**: on a node proof of kind `κ`, `ndK4 P2 P4 P8` runs `pickNd κ P2 P4 P8` after
  `kindNd4` (`kindNd4_sem`: `rF2`/`rF4` are the tests `byte = N2.byte`/`N4.byte` of tape word 5's low
  byte, the heap and output kept).
- **`safe_decF04`**, **`cost_le_decF04`**: `≤ 18,866,590,018,289 + 2,558 t` (`N2`),
  `≤ 75,140,093,025,947 + 2,558 t` (`N4`, `N8`); `decBudget4 t = 211,105,695,662,080 + 8,176 t`.
  `sizeIR (decF04 κ) = 56,236` (compiled `#eval`, `logs/fr-build-SH4e/scratch/T3.lean`; a `decide +kernel`
  proof costs 10.1 s of kernel time, so no theorem yet: §6).

### 3. Statement changes (every one)

- `FRX4Prog`: **`DecOk4.cost : ∀ t, cost nd t ≤ decBudget4 t`** (was `decBudget`);
  **`ext4With nd := toProg memX4 mpwX (ext4IRWith nd)`** (was `memX`);
  **`fuel_covers4 (h : ∀ t, cost nd t ≤ decBudget4 t) : memX4 + mpwX t + cost (ext4IRWith nd) t + 8 ≤
  fuel t`** (was `decBudget`, `memX`). `decOk4_ndNone : DecOk4 ndNone` keeps its statement (its proof
  now uses `decBudget4`). As Part 28 §7's patch list, with `memX4`/`decBudget4` defined in `FRXProg`
  (§5.2).
- `FRX4Ext`: `st1` (the state after the parse) starts from `initSt (memX4 + mpwX t)`; `den4_split`,
  `den4_W`, `den4_bad`, `den4_node`, `den4_agg` state `den memX4 mpwX …`; `Ed4 nd := Eden memX4 mpwX …`.
  Nothing else (`E4X`, `computes4`, `NodeDec4`, `nodeExt_E4X`, `ks4_E4X` unchanged in form).
- `FRXSeed`: `seedPay_length`, `tape_seed` take `48 ≤ π.size` instead of `π.size = piSize` (weaker
  hypothesis; their only users are in `FRXSeed`). `seedVal_eq`, `seedOK_seedIR` keep their statements.
- `FRSubmission4`, `FRSubmission4Cert`: unchanged. `sub4.ext = ext4With ndNone` now runs on
  `2^28 + 3t` words.

### 4. Controls

| Control | Kind | What it shows |
|---|---|---|
| `keepR4_ctl` | + / − | `KeepR4` holds on the basis table, the chain's answers, level 0's word, the index; not on either map's decoded rows nor on levels 1–4's word |
| `readK4_ctl` | value | the read's height is the kind's (`sib₀ = 10` at `N2`, 11 at `N4`); the cap depths agree |
| `decLevels4_ctl` | − / + | `N2`'s five levels are not `N4`'s (different exact costs); `N8`'s are `N4`'s |
| `cost_decLevels4` | value | the exact costs, equal to the fuel model's |
| `msgOkB_ctl` | − / + | a misaligned message and one past the proof's end are rejected; the seed's `hdr` is accepted |
| `fsMsgs4_items`, `fsMsgs4_aligned`, `fsMsgs4_length` | + | the 482 targets have `seq4`'s Fiat–Shamir kinds and lengths; all aligned inside 798,192 bytes |
| `fsMsgs4_ctl`, `fsQ4_ctl` | value / − | position 2 absorbs `cap₀` (π bytes 19,872 … + 16,384), position 3 is a squeeze, not an absorb |
| `tabEnt4_ctl`, `cbS4_ctl`, `nRep4_ctl` | value / − | the table entry of `cap₀`; the P1 challenges' words per level (distinct); the replayed positions cover P1.4 |
| `fmt4_vals`, `fmt4_ctl` | value | `pL4 = 99,779`; the caps at 19,872, 36,256, 44,448, 52,640, 60,832; the final message at 64,928; each is the absorb's range in `fsMsgs4 seq4` |
| `capFO4_ctl` | − | level 1's cap starts `32·2^9` bytes after level 0's, not `32·2^8` |
| `kindNd4_ctl` | + / − | on `N2`'s byte `rF2 = 1`, `rF4 = 0`; on `N4`'s the reverse; `pickNd` takes the kind's branch |
| `decF04_ctl` | − | `N2`'s decode is not `N4`'s |

### 5. Deviations and findings

1. **`omega` and `C + n` with a non-reducible constant `C` (finding, journal 86).** `map4.tb + 800 ≤ x ⊢
   map4.tb ≤ x` hits "maximum recursion depth": `omega` reduces `C + 800` at reducible transparency,
   cannot unfold `C`, and unfolds `Nat.add` on the literal digit by digit. `map4` is now an `abbrev`, and
   proofs carry `map4_nums`. Any later module that puts a `def` constant plus a literal ≥ 512 into an
   `omega` goal will meet this.
2. **`memX4` lives in `FRXProg`, not `FRX4Prog`** (Part 28 §7 put it in `FRX4Prog`). `FRXProg` is
   imported by both `FRX4Prog` and the decoder modules, so the one definition needs no new import edge;
   it is a `def` with the literal value `268,435,456` (`memX4_eq`), so `omega` treats it as an atom with
   a value and nothing evaluates `2^28` (`initSt (memX4 + …)` stays folded, journal 62's pitfall).
3. **The plug's memory half applied now, with `ndNone`.** `FRX4Ext`'s proofs went through unchanged at
   `memX4` (only the `simp only [regs, memX]` side conditions). The remaining plug is `nd` itself.
4. **The chain is parametric in `S` and `N`**; the `seq4` facts (`fsMsgs4_aligned`, `nRep4`, `cbS4`) are
   instances. On `v4/rev44` the same module serves with that branch's `seq4` (the decided controls and
   `fmt4_vals`' numerals change).
5. **The node-byte dispatch is in the decode module**, not in `decLevels4`: the output also depends on the
   kind (`N2`, `N4`, `N8` have different children), so `nd` will be one `ndK4` over three full branches.
6. **Not done (item 6):** the `tgBody_sem` split. Diagnosis (`logs/S-H4e/trace-FRXLagT.log`): of
   `tgBody_sem`'s 21.6 s, 14.8 s is the final `refine ⟨fun c hc => ?_, i7, …⟩`, whose expected type still
   holds the ungeneralised nested states from the `M3` step on: `generalize runPrims ([.const lgQ 1, …] ++
   zeroPs C) s2.M = M3 at … ⊢` does not abstract the goal's occurrence (a probe with `runPrims _ s2.M`
   matched nothing either), so every later `generalize` misses the goal too and the refine pays a
   defeq over the whole state. The line reflow of the new modules (65 + 5 + 14 lines over 100 columns,
   from the long `Snd.CKind.lv (.node κ) i` terms) is not done either.
7. **`FRXChain4`'s kernel time**: ≈ 12 s in one `decide +kernel` (`fsMsgs4_items` or `fsMsgs4_aligned`:
   each evaluates `fsMsgs4 seq4`, recomputing `fieldOffOf`/`phaseOffOf` per message). One shared literal
   (`fsMsgs4 seq4 = [...]`, decided once) would halve it; a structural proof of alignment would remove it.

### 6. Handover: what remains, in order

1. **`FRXOut4`, the output (item 3).** Two halves.
   - **The 4.1 proof decoder** `reassemble4 S (aB : ℕ) : Trace → Proof`, field by field (3.x's
     `FRNodeReadW.ctbs` over `phasesOf S`/`Sh`), with **row 18's size `aB` a parameter** (0 on main:
     `nFields = 18`; 45,088 on `v4/rev44`). The queries' fields need the kind's heights: π has `L.sib`
     (`seq4`'s, `m* = 32`) sibling slots per position, the kind fills `K.sib` and the rest are zero
     (`posOps4`); the position answers use the kind's `per = 256 / K.logN`. `reassemble4` is `rd4`'s
     `pf` (`FRNodeRead4`: "S-H4's reassembly, a parameter here"); **S-N2 must use the same `pf`** in its
     `NodeResid4` instance, so agree the definition with S-N2 first.
   - **`readW4 κ L es := .node c₁ c₂ (sgn4 reassemble4 κ 0 w) (sgn4 reassemble4 κ 1 w)`** with `w` the
     `Asg` of `f⁽⁰⁾`'s rows 4–7 (`w e` from `T4.msgOf (.node κ) L es 0 (4 + e mod 4) (e / 4)`, stream
     cell `e` = row `4 + e mod 4`, column `e / 4`, `FRBlockStream.elem_slot`). **Open: where `c₁`, `c₂`
     come from.** S-N2's `StmtN4` binds them through `PubCells4 κ w vk c₁ c₂` (`cells4 κ`); if those
     cells are outside rows 4–7 the decoder (which decodes only rows 4–7 at level 0) cannot read them,
     and they must come from π's `stmt` field (bytes 1–64; the node's `stmtOps4` asserts 65–127 zero
     and `c = nodeStmt c₁ c₂` through `hashStmt`). Decide with S-N2.
   - **`outIR4 κ`**: 3.x's `segIR` machinery (`FRXOut`, `FRXOutRun`) emits `witWords` from a `Seg`
     description over an address shape `addrW ap R n = R + (((n >>> 1) &&& m₁) <<< 18) + …`. The row
     stride `18` is 3.x's (`2^(mLog 0 + 1)` at `m = 30`); at 4.1 it is `2^20` (`m = 32`) or `2^19`
     (`m = 31`): generalise `addrW`/`AP` over the stride in place (pass 5's rule). The source is level
     0's rows 4–7 at `map4.l0.ob` (`decF04_sem`'s conclusion; `outIR4` stores nothing, as 3.x's).
2. **`FRXNd4` (item 4):** `nd := ndK4 (.seq (decF04 .N2) (outIR4 .N2)) (.seq (decF04 .N4) (outIR4 .N4))
   (.seq (decF04 .N8) (outIR4 .N8))`.
   - `decOk4_nd : DecOk4 nd`: `wf` (`wf_kindNd4`, `wf_decF04`), `safe` (`safe_decF04`, `kindNd4` and the
     outputs have no tape loop), `cost` (`cost_le_decF04` + the output's + 17 ≤ `decBudget4`: ample,
     `7.5·10^13` against `2.1·10^14`), `outs` (`outs_decF04 = 0` + the output's ≤ `outCap`), `size`
     (`3 · 56,236` + the outputs ≤ `2^19`; prove `sizeIR (decF04 κ)` from component lemmas, not by a
     10 s `decide +kernel`).
   - `nodeDec4_nd : NodeDec4 nd` with `Links κ L es π c := ¬ StateHit L ∧ (∀ p < nRep4, fmAns (fsQ4 seq4
     (vkOf π) c π) zeroD L p = some (ansAt es p)) ∧ (∀ i < 5, ∀ e < 2^cap, T4.capDig es i e = capPi4 i π e)
     ∧ (∀ x < 2^mLog 4, T4.finalAt es x = finPi4 π x) ∧ (∀ i < 5, ¬ T4.farL …) ∧ (∀ i < 5, A_c =
     jointAgree)` (exactly `decF04_sem`'s hypotheses), `readW := readW4`, and `out` from `ndK4_sem`,
     `decF04_sem` (at `st1`: `Inv`, size `memX4 + 3t ≥ memX4 + 2|L|`, empty output) and `outIR4_sem`.
3. **The plug (item 5's rest):** `FRSubmission4`: `ext := ext4With nd`, `sub4.E := E4X nd sub0.acc`
   (and `sub4_E`, `sub4_ext`); `FRSubmission4Cert`: `Open4.resid : ∀ vk, Resid4H … sub4 nd nodeDec4_nd vk`
   (the `∃ D` goes), `certificate_sub4` with `decOk4_nd`. Then `FR.lean` imports `FRXNd4`.
4. **Item 6:** the `tgBody_sem` fix (§5.6: name the `M3` list from the goal, e.g. state each phase as
   its own lemma on a bare memory, as Part 27 §1 planned); `FRXChain4`'s kernel time (§5.7); the line
   reflow; a `sizeIR` lemma set for the decoder's programs.

### 7. Checks (logs in `logs/S-H4e/`)

- **Build.** `lake build FR Solution FRSubmission4Cert FRXDec4F0 FRXDec4Lv FRXLagT` green on HEAD +
  this pass: **2,592 jobs** (`build-final.log`). `FRX4Ext` and the decoder modules after the `FRXProg`
  edit: 2,372 jobs (`build1.log`).
- **Axioms** (`axioms.log`, `logs/fr-build-SH4e/ax/AxSH4e.lean`, 45 declarations: every main theorem and
  control of the pass, `decOk4_ndNone`, `fuel_covers4`, `computes4`, **`certificate_sub4`**,
  **`RecursionFast.Challenge.certified`**): all within `propext`, `Classical.choice`, `Quot.sound`
  (some controls use fewer or none); no `sorryAx`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`,
  `source-rule.log`): 372 files, 0 findings.
- **Profiles**: §1's table (sequential, one module at a time, load from other agents' jobs).

### 8. Open questions

- **Q1.** `c₁`, `c₂` of the node witness (§6.1): from `f⁽⁰⁾`'s public cells (then they must lie in rows
  4–7, or level 0 must decode more rows) or from π's `stmt` field? The answer fixes `readW4` and S-N2's
  side of the links.
- **Q2.** `sub4.ext` now runs on `2^28 + 3t` words (2 GiB of 8-byte words before the tape). The contract
  only bounds the fuel; if a runner or the badge ever evaluates `ext`/`E` on a domain input, it allocates
  that array. Accept (Part 25 F2's ruling), or keep `ndNone`'s branch at `memX` until `nd` lands?

## Part 31 (track S-H4, pass 7): level 0 decodes rows 1–7; the output's cell map, `reassemble4`, `readW4`; `Open4` over S-E13a's route; handover

**Status.** HEAD `5f39f5a`, build tree `logs/fr-build-SH4f` (`MINE` = pass 6's + `FRXOut4 FRSubmission4
FRSubmission4Cert`), logs `logs/S-H4f/`. Nothing committed. **`nd` does not exist yet**: `outIR4` (the
output program and its semantics) is not written, so `NodeDec4 nd`, `decOk4_nd` and the plug of `nd` are
not done, and `Open4` still carries `∃ D : NodeDec4 ndNone` (the entry stays PROVISIONAL). What this pass
did: (1) found and fixed a blocker in the rows the decoder decodes; (2) the pure half of `FRXOut4`
(the heap-to-witness map, the computable segment count, the statements, `reassemble4` with `PfHdr`, the
decoder's `Links` and `readW`); (3) the coordinator's PATH-review changes to `Open4`/`certificate_sub4`.

### 1. Finding F1: rows 4–7 do not hold what `readW` reads (fixed: level 0 decodes rows 1–7)

Level 0 has 64 rows (`ladderOfR 6`); cell `e` of `f` is coefficient `e / 64` of row `e mod 64`. H's
message slots are rows 4–7 (revision 4.3's (A)(ii)), but:

- **the aggregates' segment count** `kAct κ a w` (`FRNodeRead4`) is the first sub-slot whose selector sum
  `selSum κ σ = Σ_ι w (κ.oneCell + selR σ ι)` is not 1. Those cells are in rows 1–3 (`oneCell ≡ 0 mod
  128`, `selR σ ι = σ·2^20 + 1 + selIx ι`). Nothing in H's messages determines `k` (S-E13b's `k`-mux reads
  `selSum` too);
- **an aggregate's statement** `stC κ σ h = cAB κ a · 128 + 2 + h` (the `c_A` block's `h_out`, `PubCells4`'s
  cell) is in rows 2–3;
- (as the blueprint already says) L's signature cells cover all 64 rows, so the signature is read from H
  (`sig_of_H`).

`out_cells_rows` checks the three facts in the kernel. **Fix, inside S-H4's modules:** level 0 decodes rows
`1 … 7` (`c₀ = 1`, `C = 7`; `decLv4_sem` is parametric). Cost: `+8.25·10^12` at `N2`, `+3.30·10^13` at
`N4`/`N8`; the decode is now `≤ 1.081·10^14 + 2,558 t` against `decBudget4 t = 2.111·10^14 + 8,176 t`.
Rows 1–7 hold every cell the output reads except L (`out_cells_dec0`), so the statements and `k` need no
link (Q1, below). This is a deviation from (A)(ii)'s "4 rows" (cost estimate `1.4–1.6·10^14` there; measured
model now `1.08·10^14`).

### 2. Files (`loc.py`: total / comment / blank / code / theorems)

| File | loc | Content |
|---|---|---|
| `FRXOut4` (new) | 388 / 51 / 84 / 253 / 20 | `Dec0`, `wF`, `wAddr`, `cells_cols`, **`decF04_wF`**; `msg_dec0`, **`out_cells_dec0`**, **`out_cells_rows`**; **`kSel`**, `find_range_getD`, **`kSel_eq`**; **`stD`**, **`stD_of_pubCells`**; `qB4`, `trM4`, `sib4`, `posOf4`, `ctb4`, `ansOf4`, `ctbs4`, **`reassemble4`**, `aBytes4`, **`pf4`**, `fitL_extract_getD`, **`pfHdr_reassemble4`**, `ctb4_length`, `ctbs4_length`, **`reassemble4_size`**; **`LinksD4`**, **`sgnX`**, **`readW4`**, `sgnX_eq`, **`readW4_eq`**; controls. 11.6 s sequential (`cpu-FRXOut4.txt`). |
| `FRXDec4Map` | 202 / – / – / 108 / 16 (−1 code) | `map4.l0` re-laid for 7 rows (`ob = 26,214,400`, `eb = 34,603,008`, `xb = 34,603,264`, `yb = 36,700,416`); `Map4.Ok`'s level 0 at `C = 7`; `map4_ctl`, `not_map4_slack`, `map4_l0` restated. |
| `FRXDec4Levels` | 677 / – / – / 507 / 35 (±0) | `dec04` at `7 1`; `map4_nums`, `lv0Step4_sem`, `decLevels4_sem`, `cost_dec04`, `cost_decLevels4` restated (§4). |
| `FRXDec4F0` | 393 / – / – / 273 / 19 (±0) | `decF04_sem`, `cost_le_decF04` restated (§4). |
| `FRSubmission4Cert` | 104 / – / – / 48 / 6 (+18 code) | `Vnode4`, **`Links4`**, **`Gaps4`**, `Open4` (new fields), `pfHdr_pf4`, **`resid4H_of`**, `certificate_sub4` (new proof), `not_boundsOK_qV` at `qV4 − 1`; imports `FRNodeRows4PackSound`, `FRXOut4`. |

### 3. What is proved

- **`decF04_wF`**: under `decF04_sem`'s hypotheses, after `decF04 κ`, every cell `e` with `1 ≤ e mod 64 < 8`
  and `e < 2^(m − 7)` sits at `wAddr κ e = map4.l0.ob + 2^(mLog 0 + 1)(e mod 64 − 1) + 2⌊e/64⌋` as
  `wF κ L es e`, which is `T4.fF (.node κ) L es e` (S-G's witness, `fTab` unfolded).
- **`kSel_eq`**: the computable `kSel κ a w` (first `i < maxK` with `selSum … ≠ 1`, else `maxK`) is `kAct`.
- **`stD_of_pubCells`**: on `PubCells4 κ w vk c₁ c₂`, the cells `stC κ σ 0, 1` read back `c₁`, `c₂`.
- **`reassemble4 S aB tr`** (the slots' `pf`, `pf4 := reassemble4 seq4 aBytes4`, `aBytes4 = 0` on main): 3.x's
  field-by-field `ctbs` over `phasesOf S` with the kind's ladder for the siblings (`sib4`: the node query's
  half by the position bit below `K.sib`, 32 zero bytes above it, `posOps4`'s rule) and the positions
  (`posOf4`: `per`, `logN` of `S.lvK m i`); field 18 fitted to `aB`. Every contribution is fitted to its size
  (`qB4`), so **`reassemble4_size`**: `|reassemble4 S aB tr| = piSizeOf S + aB` on every trace, and
  **`pfHdr_reassemble4`**: byte 0 is byte 71 of the seed query (S-E13a's `PfHdr`, unconditionally; a 3.x-style
  `extract` is short on a short seed query and breaks it).
- **`readW4 sg κ L es := .node (stD κ 0 w) (stD κ 1 w) (sgnX sg κ 0 w) (sgnX sg κ 1 w)`**, `w = wF κ L es`,
  `sgnX` = the reader's proof and trace (`rd4 pf4`) with the signature by `sg` (H's cell map).
  **`readW4_eq`**: on `PubCells4` and `sg = readSig4` (`sig_of_H`), `readW4 sg κ L es = .node c₁ c₂ ((rd4
  pf4).sgn κ 0 w) ((rd4 pf4).sgn κ 1 w)`, the witness `node_sound4` proves related. This is the bridge S-L4's
  `hL_of_res` needs.
- **`LinksD4 κ L es π c`**: `decF04_sem`'s hypotheses (`¬ StateHit L`, the chain with an existential initial
  state, caps, final message, `¬ farL`, `A_c = jointAgree`): the `Links` of the coming `nodeDec4_nd`.
- **`resid4H_of`**: `Gaps4` and `Links4 nd D` give `Resid4H … sub4 nd D vk` (slots `I4`, `rd4 pf4`,
  `resid4_of ∘ gap4_of_rows pf4 pfHdr_pf4`).

### 4. Statement changes (every one)

- `Map4.Ok`: level 0's conjunct at `C = 7` (was 4). `map4` (the literal): `l0`'s `ob`, `eb`, `xb`, `yb`.
  `map4_ctl`: `map4.l0.eb = 2^25 + 2^20` (was `2^25`). `not_map4_slack`: the perturbed `eb` is
  `26,214,400 + 2·2^19·7`. `map4_l0`: `… 7 64`.
- `map4_nums`: `l0.ob = 26214400`, `l0.eb = 34603008`, `l0.xb = 34603264`, `l0.yb = 36700416`.
- `lv0Step4_sem`, `decLevels4_sem`, `decF04_sem`: conclusion `∀ q < 7, … = msgOf (.node κ) L es 0 (1 + q) x`
  (was `q < 4`, `4 + q`). Hypotheses unchanged.
- `cost_dec04`: `72 * 7`, `40 * 7`, `7 * (17 + …)` (was 4). `cost_decLevels4`: `27,032,496,972,783` (`N2`),
  `108,050,895,689,694` (`N4`, `N8`). `cost_le_decF04`: `27032496972783 + …`, `108050895689694 + …`.
- **`Open4`** (was `resid : ∃ D : NodeDec4 ndNone, ∀ vk, Resid4H … sub4 ndNone D vk`): now
  `gap : Gaps4` and `dec : ∃ D : NodeDec4 ndNone, Links4 ndNone D`. Equivalent content routed through
  S-E13a's `Gap4R` (strictly weaker than `Resid4H.slots`: `PfHdr`, `kindN`, `kindS@0`, `wf@0`, `wots`,
  `aggPad` are theorems), at the fixed `pf4`.
- `certificate_sub4`, `certificateR_sub4`, `Solution.certified`: same statements (`Open4 → …`), new proof of
  `certificate_sub4` (`resid4H_of`).
- `not_boundsOK_qV`: query bound `qV4 − 1` (was the literal `35999`).

### 5. Controls

| Control | Kind | What it shows |
|---|---|---|
| `out_cells_dec0` | + | every selector cell and both statements' cells are in rows 1–7 |
| `out_cells_rows` | − / value | a selector is in row 1, an aggregate's statement cell in row 2 (outside 4–7); L's first signature cell is not decoded |
| `kSel_ctl` | − / + | on the zero witness `kSel = 0`; `kSel ≤ maxK` |
| `pf4_size` | value | `|pf4 tr| = 798,192` on every trace |
| `pf4_hdr_ctl` | + / − | a seed query with `N4`'s byte at 71 gives a proof starting with it; an all-zero seed does not |
| `readW4_eq`, `stD_of_pubCells`, `kSel_eq`, `decF04_wF` | + (universal) | the output's map agrees with the reader's and the decode's |
| `not_map4_slack` | − | level 0's `eq` table at the end of 7 rows (no `2k` slack) is rejected |
| `map4_ok31`, `map4_ok32` | + | the 7-row map is sound at both ladders |
| `not_boundsOK_qV` | − | a declared query bound `qV4 − 1` fails the bounds |

### 6. Checks (logs in `logs/S-H4f/`)

- **Build:** `lake build FR Solution FRSubmission4Cert FRXOut4 FRXDec4F0 FRXLagT` green, **2,593 jobs**
  (`build-final.log`; baseline `build0.log`, 2,592).
- **Axioms** (`axioms.log`, `logs/fr-build-SH4f/ax/AxSH4f.lean`, 28 declarations incl. **`certificate_sub4`**,
  **`RecursionFast.Challenge.certified`**, `resid4H_of`, `decF04_sem`, `decLevels4_sem`, `cost_le_decF04`):
  within `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- **Source rule** (`source-rule.log`): 373 files, 0 findings.

### 7. What `Open4` assumes after this pass (exact)

1. `gap : Gaps4` — `∀ vk κ w c₁ c₂, StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w → Gap4R implB (fun _ =>
   implB) pf4 κ vk c₁ c₂ w`: `imp` (`SlotImp`), `kindS` and `wf` at sub-slots `i ≥ 1`, `aggChk`. Owners
   B1′ … B4, A1′ (PATH-review F1 rows 4–6). `PfHdr pf4` is discharged (`pfHdr_pf4`).
2. `dec : ∃ D : NodeDec4 ndNone, Links4 ndNone D` — unsatisfiable while an accepted node proof lies in the
   domain (`not_nodeDec4_ndNone`). When `nd` lands it becomes `Links4 nd nodeDec4_nd` with
   `nodeDec4_nd.Links = LinksD4` and `.readW = readW4 sg` (S-L4: `hL_of_res`, via `readW4_eq`, which needs
   `sig_of_H` for the chosen `sg`).

`DecOk4` is proved (`decOk4_ndNone`; `decOk4_nd` when `nd` lands). Everything else of
`certificate_rev4H` is closed.

### 8. Deviations

1. **Level 0 decodes rows 1–7, not 4–7** (§1; BLUEPRINT (A)(ii)). Reason: `k` and `c_A` are only in rows 1–3;
   within budget.
2. **`Open4` fixes `pf := pf4`** instead of the review's `∃ pf, PfHdr pf ∧ …`: `readW4` reads the slots'
   proofs with `pf4`, so `Links4` (whose `Rel` is about `readW`) is provable only at the same `pf`; `PfHdr
   pf4` is a theorem.
3. **`readW4`'s signature reader `sg` is a parameter.** The H fields (`ots_i` = the `x` field of chain block
   `w_{i,0}`, the path blocks' `l`/`r` by the index bit, the index from the key leaf's `j` field) are S-E's
   layout (`FRNodeRows4WotsS`'s link families); S-G/S-E own `sig_of_H` (BLUEPRINT §(A)). `nd` needs a fixed
   `sg`.
4. **The statements come from the cells** (`stD`), not from π's `stmt` bytes (Q1 ruling: the option without a
   new hypothesis; `stD_of_pubCells` makes S-L4's side a rewrite, and `NodeLog`'s `c = nodeStmt (stL es 0)
   (stL es 1)` with `PubCells4` at `pvL` closes `Rel`'s first conjunct).
5. **`reassemble4`'s `aB`** fits field 18's contributions (`ctbs4 … 18`) to `aB` bytes; on main no phase
   writes field 18 and `aBytes4 = 0`.
6. Not done: item 4 (`tgBody_sem` split, reflow), `FRX4Prog`'s literal `798192` in `szPs`/`kindOf4_node`
   (PATH-review F4.5: to restate through `piSizeOf seq4` during the rev44 port).

### 9. Handover: what remains, in order

1. **Fix `sg`** (with S-E/S-G): `sigH κ σ w : Sig` over H message cells (rows 4–7), per §8.3. If S-E prefers,
   move the signature into H blocks (BLUEPRINT's alternative). State `sig_of_H : StmtN4 … → ∀ σ < 2, sigH κ σ w
   = readSig4 κ σ w` as S-G/S-E's obligation (it feeds `readW4_eq`).
2. **`outIR4 κ`** (`FRXOut4`, second half; 3.x's `FRNodeReadS`/`FRNodeReadP`/`FRXOut`/`FRXOutRun`, ≈ 2,000 code
   lines there). The words of `witWords (readW4 sigH κ L es)`, all loads from `wAddr` (`decF04_wF`):
   - tag `1`; `packBytes (stD κ σ w) = elemWords (w (stC κ σ 0)) ++ elemWords (w (stC κ σ 1))`
     (`packBytes_digestOf`), four loads each;
   - per signed child: `bytesWords π` (length word `|π|`, then π's words), `logWords tr`, `sigWords σ`.
     A previous node: `π = fitL piSize (pf4 (segTr κ 0 0 0 w))` (exactly `piSize` bytes, `pf4_size`), `tr =
     segTr`. An aggregate: `k = kSel κ a w` computed at run time (three selector loads, XOR, compare with
     `1`, per sub-slot); `π = aggHdr k n e ++ k slot proofs` (`n`, `e` from `hA`, the `cAB` block's message);
     `tr = k segment traces`. Unroll over `i < maxK` with an `ite` on `i < k` (`maxK ≤ 4`).
   - The stream words: stream byte `p` of `chainBytes4 κ σ k w` is byte `p mod 16` of cell
     `blkOf κ σ k ⌊p/64⌋ · 128 + 4 + (p mod 64)/16`. Segment `i` starts at byte `1 + i(segB − 1)`, i.e.
     `1 − i mod 8`: words straddle cells by a segment-dependent shift (3.x's `shw`). The last stream block
     of an aggregate with `k < maxK` is `finBlk` (not the main chain's): the address map is per `(σ, k)`.
   - The proof bytes (`ctbs4` over `phasesOf seq4`) are fixed slices of item queries, i.e. of stream bytes,
     plus the sibling choice (`sib4`, a bit of an answer word) and zero padding: 3.x's `proof_words` at
     `seq4`, with the kind's ladder from stream byte `1 + 71 + …` (the seed query's byte 71).
   - Generalise `FRXOut.addrW`'s row stride `<<< 18` to a parameter (here `2^(mLog 0 + 1)`, `2^20`/`2^19`)
     in place, and the row offset `e mod 64 − 1`.
3. **`FRXNd4`:** `nd := ndK4 (.seq (decF04 .N2) (outIR4 .N2)) (.seq (decF04 .N4) (outIR4 .N4)) (.seq
   (decF04 .N8) (outIR4 .N8))`; `decOk4_nd` (cost: `cost_le_decF04` + the output's, `≤ 1.09·10^14 + 2,558 t`
   leaves `≈ 10^14` for it); `nodeDec4_nd := ⟨LinksD4, readW4 sigH, out⟩` with `out` from `ndK4_sem`,
   `decF04_wF` (domain facts: `kindOf4_node` gives the size, `InDomE` the tape bounds, `st1` the state) and
   `outIR4_sem`.
4. **The plug:** `sub0.ext := ext4With nd`, `sub4.E := E4X nd sub0.acc`; `Open4.dec : Links4 nd nodeDec4_nd`
   (the `∃ D` goes); `certificate_sub4` with `decOk4_nd`, `nodeDec4_nd`. One-line changes now
   (`resid4H_of` is generic in `nd`, `D`).
5. Item 4 of Part 30 §6 (`tgBody_sem`, reflow), unchanged.

### 10. Open questions

- **Q1 (for the orchestrator / S-E).** Accept rows 1–7 at level 0 (§1, §8.1), or have S-E put `k` and `c_A`
  into H message slots and keep 4 rows? The decoder side is done for rows 1–7; the alternative needs circuit
  rows and changes `kAct`'s definition.
- **Q2 (S-E/S-G).** Which H cells are the signature (§8.3, §9.1)? `nd` cannot be written before `sg` is fixed.

## Part 32 (track S-H4, pass 8): the signature reader `sigH` and `sig_of_H`; the signature's output words; handover for `outIR4`

**Status.** HEAD `b562c50`, build tree `logs/fr-build-SH4g` (`MINE` = pass 7's + `FRXSig4 FRXSig4H
FRXSig4W`), logs `logs/S-H4g/`. Nothing committed. **Item 1 (Q2 ruling) is done with no new
hypothesis**: `sg := sigH`, `sig_of_H` from `StmtN4` alone. Item 2 is started (the signature's output
words, pure, and the heap address of H's message words). **`outIR4` (traces, proofs, `π_A`), `FRXNd4`
and the plug are not done**; `Open4` is unchanged (`dec` still over `ndNone`).

### 1. Files (`loc.py`: total / blank / comment / code / theorems)

| File | loc | Content |
|---|---|---|
| `FRXSig4` (new) | 73 / 18 / 29 / 26 / 3 | `hMB` (H message byte), `hMD`, **`idxH`**, `rFH`, `sibFH`, **`sigH`**; `hMB_eq` (= `msgBytes` byte), **`hMB_dec0`** (every cell read is in rows 4–7); `wIdx1`, **`sigH_ctl`**. |
| `FRXSig4H` (new) | 161 / 13 / 26 / 122 / 6 | **`xRows_of_stmt`**, **`idxH_eq`**, **`otsH_eq`**, **`sibFH_eq`**, **`sig_of_H`**, **`readW4_sigH`**. |
| `FRXSig4W` (new) | 252 / 30 / 46 / 176 / 14 | `hMBs`, **`hMW`**, **`shWd`**, `wOf`; `wordBytes_getD`, `elemWords_byte`, `hMW_byte`, `wOf_eq`, `shift_digit`, **`shWd_byte`**, `wOf_congr`, **`wOf_hMBs`**, `packBytes_ofFn32`, **`packBytes_hMBs`**, `hMBs_blk`, **`sigWords_sigH`**; **`hAddr`**, **`hAddr_eq`**, **`hMW_heap`**. |
| `FRSubmission4Cert` | 110 / – / – / 50 / 6 (+2 code) | imports `FRXSig4H`, `FRXSig4W`; module doc. No statement changed. |

### 2. `sigH` (revision 4.3 (A)(ii), the H rows checked)

`sigH κ σ w : Sig` reads only H message slots (`hMB w b p` = byte `p mod 16` of element `4 + ⌊p/16⌋` of
block `b`, i.e. rows 4–7 of `f⁽⁰⁾`: `hMB_dec0`), WOTS block `o` = `W4.wb κ σ o`:

- `idx` = `ofLE` of message bytes 1–8 of block `399` (the key leaf's `j` field);
- `ots_i` = message bytes 11–42 of block `3i` (chain `i`'s first step block, its `x` field);
- `path_t` = the `l` field (bytes 1–32 of block `466 + 2t`) if bit `t` of `idx` is `1`, else the `r` field
  (bytes 33–63 of block `466 + 2t`, then byte 0 of block `467 + 2t`).

All of them lie in rows 4–7 (the blueprint's rows; no use of rows 1–3, no L cell).

### 3. `sig_of_H` (every H ↔ L equality has a row; none missing)

```lean
theorem sig_of_H (hS : StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    ∀ σ < 2, sigH κ σ w = N4s.readSig4 κ σ w
theorem readW4_sigH (hS : StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ (wF κ L es)) :
    readW4 sigH κ L es = .node c₁ c₂ ((N4s.rd4 pf4).sgn κ 0 (wF κ L es)) ((N4s.rd4 pf4).sgn κ 1 (wF κ L es))
```

| L field | H field | rows / families used (S-E13b) |
|---|---|---|
| `idx` (`Lc 0`, `c₀`) | key leaf bytes 1–8 | `j` family (`j_byte`), index row `mc 399 0 = Lc 0` (`j_mirror`); `ofLE_enc64` |
| `ots_i` (`Lc (1+2i)`, `+1`) | block `3i` bytes 11–42 | `x` family (`fam_byte`, `f = 0`), chain row `x_{i,0} = ots_i` (`chainRowsI`, first row) |
| `path_t` (`Lc (267+2t)`, `+1`) | `l` / `r` fields | `l`, `r0`, `r31` families (`f = 5, 6, 7`), mux rows `l = b ? sib : cur`, `r = b ? cur : sib` (`mux_rows`), index bits (`idx_bit`), `r31_byte` |

The node rows' truth comes from `StmtN4` (`xRows_of_stmt`: S-E13a's fold, `xOkK` or the rejecting row), so
**no hypothesis is added**. `readW4_sigH` is `readW4_eq` at `sg := sigH`: S-L4's `hL_of_res` can use it as is.

### 4. The signature's output words and the heap (item 2's first piece)

- **The H message word stream** `hMW w n` (word `n mod 8` of block `⌊n/8⌋`'s message) has byte `k` =
  stream byte `8n + k` (`hMW_byte`). The machine's word at a byte offset `8n + s` (`0 < s < 8`) is
  `shWd W s n = (W n >>> 8s) + (W (n + 1) <<< (64 − 8s))` (`wOf_hMBs`).
- **`sigWords_sigH`**: `sigWords (sigH κ σ w) = shWd 1 (8·b₃₉₉) :: (⋃_{i<133} [shWd 3 (8·b_{3i} + 1 + j)]_{j<4})
  ++ ⋃_{t<16} [shWd 1 (8·b_{466+2t} + (bit_t ? 0 : 4) + j)]_{j<4}` over `hMW w` (597 words).
- **`hAddr_eq`**: word `n` sits at `ob + 2^(mLog0+1)·(3 + (n >>> 1) & 3) + 4·(n >>> 3) + (n & 1)` —
  3.x's `addrW` shape `(m₁, s₃, s₄) = (3, 3, 2)` with the row shift `mLog 0 + 1` for 3.x's 18 and the base
  `ob + 3·stride`; **`hMW_heap`**: that heap word is `hMW (wF κ L es) n` after the decode (from
  `decF04_wF`'s conclusion, for blocks inside `f`).

### 5. Controls and checks

| Control | Kind | What it shows |
|---|---|---|
| `sigH_ctl` | + / − | on `wIdx1` (key leaf element 4 = 256) `sigH`'s index is 1 while L's index cell reads 0: the readers differ off the statement, so `sig_of_H` needs the rows; on the zero witness `idx = 0` (`decide +kernel`, 2.5 s) |
| `hMB_dec0` | + | every cell `sigH` reads is decoded (rows 4–7) |
| `sig_of_H`, `readW4_sigH`, `sigWords_sigH`, `hMW_heap` | + (universal) | the H reader agrees with L's on every statement's witness; its words are the heap's shifted pairs |

- **Build:** `lake build FR Solution FRSubmission4Cert FRXSig4H FRXSig4W` green, **2,601 jobs**
  (`logs/S-H4g/build1.log`; baseline `build0.log`, 2,598).
- **Axioms** (`logs/S-H4g/axioms.log`, `logs/fr-build-SH4g/ax/AxSH4g.lean`, 15 declarations incl.
  **`certificate_sub4`**, **`certificateR_sub4`**, **`RecursionFast.Challenge.certified`**, **`sig_of_H`**):
  within `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- **Source rule** (`logs/S-H4g/source-rule.log`): 380 files, 0 findings.
- **Sequential times** (`profile-*.log`): `FRXSig4` 8.8 s (kernel 2.5 s), `FRXSig4H` 7.6 s, `FRXSig4W` 11.0 s.

### 6. What `Open4` still assumes (exact; unchanged by this pass)

1. `gap : Gaps4` — `∀ vk κ w c₁ c₂, StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w → Gap4R implB (fun _ => implB)
   pf4 κ vk c₁ c₂ w` (`imp`, `kindS`/`wf` at `i ≥ 1`, `aggChk`).
2. `dec : ∃ D : NodeDec4 ndNone, Links4 ndNone D` — unsatisfiable while `nd` is missing (`not_nodeDec4_ndNone`).
   When `nd` lands: `Links4 nd nodeDec4_nd`, with `nodeDec4_nd = ⟨LinksD4, readW4 sigH, out⟩`; S-L4's side is
   then `readW4_sigH` + `LinksD4`.

### 7. Deviations

1. None in the statements. The names `hMB`/`rFH`/`sibFH`/`shWd` avoid 3.x's `FR.X.hB`, `rH`, `sibH` and
   `FR.shW`.
2. `sigH` uses the `r` field's byte 31 from block `467 + 2t` (the `r31` family's source), as the blueprint's
   (A)(ii) "path blocks' `l`/`r` fields" implies; `sibFH` chooses by the index read off H (`idxH`).

### 8. Handover: what remains, in order (the design worked out this pass)

**Key fact.** Signed child `σ`'s chain stream is H's message byte stream too: stream byte `p` of
`chainBytes4 κ σ k w` is `hMBs w (64·chBase κ σ + p)` for `p < 64·(streamL − 1)`, and its last block is
`blkOf … (streamL − 1)` (= `finBlk κ σ k`; for a previous node and for `k = maxK` this is again `chBase +
streamL − 1`, contiguous). So **one loader** serves the signature, the traces, the proofs and `π_A`'s
`(n, e)` (the `cAB` block's message is H too): the shifted pair `shWd (hMW w) s n` at `hAddr`, with a
**redirect** of the last stream block to `finBlk` for an aggregate with `k < maxK`.

1. **`FRXOut`'s `AP`, in place** (FRX module, already in the certificate's closure): add the row shift `st`
   (3.x: 18) and the byte shift `sh` (3.x: 0; `shWd … 0 n = W n` since `<<< 64` is 0 — extend `shWd_byte`
   to `s = 0`), and a redirect (registers `qL`, `Δ`: add `Δ` when `n >>> 3 = qL`). Then `segIR_sem`
   (`segOut (src …)`) carries over with `src` the shifted, redirected H word; 3.x's `apS`/`apL` set
   `st = 18`, `sh = 0`, no redirect (`FRXOutRun` unchanged otherwise).
2. **Segment shifts**: segment `i` starts at stream byte `1 + i·(segB − 1)`; with `segB = streamBytesOf
   seq4 ≡ 0 mod 8` (main: `1,482,752`) the item words of segment `i` sit at byte offsets `≡ 1 − i mod 8`, i.e.
   a 3.x segment (stream byte 1 = the seed entry) over the source re-based at word `⌊i(segB − 1)/8⌋` with byte
   shift `i(segB − 1) mod 8` (`0, 7, 6, 5` for `i = 0 … 3`, on top of 3.x's own `shw` for the seed). Compile
   one copy per `i < maxK`. State through `streamBytesOf seq4` (rev44 portability), not the literal.
3. **The words** (3.x's `slotSeg`/`proof_words` at `seq4`): per signed child `bytesWords π ++ logWords tr ++
   sigWords σ`. `logWords (segTr …)`: 3.x's `logWords_tSegs` over `itemsOf seq4`; `π = fitL piSize (pf4
   tr)` = `reassemble4 seq4 0`: 3.x's `proof_words` re-done for `ctbs4` (fitted contributions `qB4`, `sib4`
   with `S.lvK m i`, `posOf4`); an aggregate's `π_A = aggHdr k n e ++ k proofs`, `n`, `e` from `hA` (the
   `cAB` block's message words, `hMW` again), `k = kSel` (three selector loads per sub-slot, rows 1–3,
   `kSel_eq`); unroll over `i < maxK` with `ite (i < k)`. The signature: `sigWords_sigH` (done) — its program
   is two loops (133 chains × 4 `shWd 3`, 16 levels × 4 `shWd 1` at offset `bit ? 0 : 4`, the bit from the
   index word kept in a register).
4. `outIR4_sem` (`= witWords (readW4 sigH κ L es)` from `decF04_wF` → `hMW_heap`), its exact cost
   (3.x's node output: 21.6 M steps; far inside the `≈ 10^14` left by `cost_le_decF04`), outs, size.
5. `FRXNd4`, the plug (Part 31 §9 items 3–4, one-line changes), item 5 (`tgBody_sem` split, reflow).

### 9. Open questions

- **Q1 (S-L4).** `readW4_sigH` takes `StmtN4` at `wF κ L es`: is that the form `hL_of_res` has, or does S-L4
  prefer `readW4_eq`'s two hypotheses (`PubCells4`, `sig_of_H`'s conclusion)? Both are available.
- **Q2 (orchestrator).** Editing `FRXOut`'s `AP` in place (§8.1) touches a 3.x module still in the
  certificate's closure (via `FRXNode`); RET may prefer a copy of `FRXOut`'s generic half (Seg compile,
  `Ctx`, loops, `ldw`) into a 4.x core module first. Which?

## Part 33 (track S-H4, pass 9): `outIR4`'s pure half (the output words as segments over each segment's realigned words); `AP.st`; handover for the machine half, `FRXNd4` and the plug

**Status.** HEAD `cb849a3`, build tree `logs/fr-build-SH4h` (copy of `fr-build-SH4g`, `snap.sh` on HEAD;
`MINE` = pass 8's + `FRXOut FRXOutRun FRXTr4 FRXPf4 FRXOut4W`), logs `logs/S-H4h/`. Nothing committed.
**Done: every pure fact `outIR4_sem` needs** — `witWords (readW4 sigH κ L es)` as the tag, the statements'
cell words, and per signed child explicit segments (`FRXOut4R`'s `segIR` input) over each segment's
realigned stream words, plus `readW4_fits`. **Not done: the machine half of `outIR4`, `FRXNd4`, the plug**
(nor the coordinator's `FRSubmission4Fin`, which needs `nd`). `Open4` is unchanged; the entry stays
PROVISIONAL. §7 is the handover.

### 1. Files (`loc.py`: total / blank / comment / code / theorems)

| File | loc | Content |
|---|---|---|
| `FRXTr4` (new) | 226 / 28 / 38 / 160 / 10 | `tPh4`, `tSegs4`, `restSh4`, **`trSeg4 S`**, **`TrOk4 S`**; `entryW_alignedL`, `readItems_wordsL`, `entryW_seedL`, `trW_eqL`, `segOut_tPh4`, `segOut_tSegs4`, `itemsOf_cons`, **`logWords_trSeg4`**, **`trOk4_seq4`**, `trOk4_ctl`. 11.1 s sequential. |
| `FRXPf4` (new) | 568 / 71 / 63 / 434 / 28 | `sOff4`, `wo4`, `nextA4`, `sibS4`, `pPh4`, `pRest4`, `fSeg4`, **`pSeg4 S m`**, `qPrev4`, `qHead4`, `qOk4`, **`PfOk4`**, **`LadOk4`**, **`mOfB`**; item/offset lemmas (`sOff4_drop`, `drop_cons_item4`, `drop_rep4`, `sOff4_slen_le`, `sOff4_mod8`, `mem_rest4`, …), `trOf`, `trOf_getD`, `qBytes4`, `fitL_self`, `cpSlice4`, `ans_bit4`, `testBit_posOf4`, `sib_one4`, `PrevInv4`, `lv_t_out`, `posItemsL_slen`, `pPh4_spec`, `pRest4_spec`, **`trM4_eq`**, **`proof_words4`**, **`pfOk4_seq4`**, **`ladOk4_seq4`**, `mOfB_mem`; controls `qOk4_ctl`, `mOfB_ctl`. 14.9 s. |
| `FRXOut4W` (new) | 339 / 50 / 41 / 248 / 32 | **`vS`**, `trBody4`, `hdrWords`; `readItems_drop`, `readItems_take`, `wordsBytes_packBytes8`, `chainBytes4_length`, `streamBytesOf_rest`, **`segTr_eq`**, `vS_length`, `pf4_words`, `logWords_segTr`, `entries_segTr`, `aggHdr_words`, `hAn_lt`, `sgnX_π`, `sgnX_tr`, `aggPf_eq`, **`signedWords_prev`**, **`signedWords_agg`**, `logWords_flatten`, **`witWords_readW4`**, `sgnX_fits`, **`readW4_fits`**. 9.3 s. |
| `FRXOut` (edited) | 1,042 / – / – / 893 / 49 (+2 lines) | `AP` gains the row shift `st`; `addrW`, `ldPs` use `toWord ap.st` where they had `18`. |
| `FRXOutRun` (edited) | 385 (±0) | `apS := ⟨3, 3, 2, 18⟩`, `apL := ⟨63, 7, 1, 18⟩`. |

New code: 842 lines (3 modules, not yet in the certificate's closure).

### 2. What is proved

- **`logWords_trSeg4`** (any `S` with `TrOk4 S`, any word list `Ws`, any `W` agreeing with it, the stream
  long enough): `logWords (readItems (wordsBytes Ws) 1 (itemsOf S)) = segOut W κ 0 (trSeg4 S)` — the count,
  the seed's entry (`seedSeg`, stream byte 1), then per later item its length word and `qlen/8 + 4` words.
- **`proof_words4`** (`PfOk4 S`, `LadOk4 S m`, `trM4 tr = m`): `bl (reassemble4 S 0 tr) = wordsBytes (segOut W κ
  0 (pSeg4 S m))` for `tr = readItems (wordsBytes Ws) 1 (itemsOf S)`; **`trM4_eq`**: `trM4 tr = mOfB` of word
  10's low byte. Only field 17 (`fSibs`, the last) depends on `m`.
- **`segTr_eq`**: segment `i`'s trace is `trOf seq4 (vS κ σ k i w)` whenever `i(segB − 1) + segB ≤ streamB κ σ k`
  (the bytes before and after it are not read: `readItems_drop`, `readItems_take`).
- **`signedWords_prev`** (`κ.hasPrev`, child 0) and **`signedWords_agg`** (aggregate `a < nAgg κ`, `k = kSel κ a w`,
  any `V i` agreeing with `vS … i`):
  `signedWords (sgnX sigH κ σ w)` = `|π|`, the proofs' segments, the count, the traces' bodies, then
  `sigWords (sigH κ σ w)` (pass 8's `sigWords_sigH` gives those as H words). The aggregate's `|π_A| = 48 +
  k·piSizeOf seq4`, its header words `hdrWords k (hAn) (hAe)` (`aggHdr_words`, `k ≤ 4`, `hAn < 2^64`), its count
  `k · |itemsOf seq4|`.
- **`witWords_readW4`**: `witWords (readW4 sigH κ L es) = 1 :: (stmt cells' words) ++ signedWords σ₀ ++ signedWords σ₁`.
- **`readW4_fits`**: `(readW4 sigH κ L es).Fits` (the `Fits` half of `NodeDec4.out`).

### 3. Statement changes (every one)

- `FRXOut.AP`: new field `st`. `addrW ap R x` shifts the row part by `ap.st` (was the literal `18`); `ldPs ap`
  likewise. Every theorem of `FRXOut`/`FRXOutRun`/`FRXNode`/`FRXNodeRun` keeps its statement (at `apS`, `apL`
  the shift is `18`); the exact costs, outs and sizes are re-decided unchanged.
- Nothing else. `Open4`, `certificate_sub4`, `certified` unchanged.

### 4. Controls

| Control | Kind | What it shows |
|---|---|---|
| `trOk4_ctl` | − | `seq4` with a 33-byte `E4end` (a 73-byte query) is not aligned |
| `trOk4_seq4`, `pfOk4_seq4`, `ladOk4_seq4` | + | `seq4`'s format meets the segment conditions at all three ladders |
| `qOk4_ctl` | − / + | a `queries` phase not after its `P2` phase is rejected; `seq4`'s table passes |
| `mOfB_ctl` | value | `L30`'s byte reads ladder 30, `N2`'s 31, `N4`'s 32, `'A'` (no kind) 32 |
| `proof_words4`, `logWords_trSeg4`, `signedWords_*`, `witWords_readW4`, `readW4_fits` | + (universal) | the output words are the segments' over each segment's words |

Measured (scratch `#eval`, `logs/S-H4h/SegSz.lean`, not in the entry): `pSeg4 seq4 32` compiles to 4,940
statements (field 17: 1,245), `trSeg4 seq4` to 4,904; 99,774 and 185,345 words; `depthSeg 1`; `okSeg` at all
three ladders; 4,186,985 and 6,603,369 steps.

### 5. Checks (logs in `logs/S-H4h/`)

- **Build:** `lake build FR Solution FRSubmission4Cert FRXOut4W` green, **2,609 jobs** (`build-final.log`;
  baseline `build0.log`, 2,602).
- **Axioms** (`axioms.log`, `logs/fr-build-SH4h/ax/AxSH4h.lean`, 20 declarations incl. **`certificate_sub4`**,
  **`RecursionFast.Challenge.certified`**, `proof_words4`, `signedWords_agg`, `readW4_fits`, `cost_outIR`):
  within `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- **Source rule** (`source-rule.log`): 384 files, 0 findings.

### 6. Deviations

1. **The byte shifts and the `finBlk` redirect are not in `AP`** (the pass-8 ruling's letter): the output
   will copy `finBlk`'s 8 message words onto the main chain's last block and realign each segment into an
   aligned buffer, then run `segIR` unchanged over the buffer (linear shape `⟨0, 1, 1, _⟩`). Reason: a shift
   in `ldw` needs scratch and parameter registers that `LW`/`OW`/`Prot`/`Ctx` would have to admit, i.e. every
   3.x segment proof re-threaded; the buffer keeps `segIR_sem` literally as is. `AP` gains only the row
   stride (`st`), which the H loader needs. 3.x's statements unchanged (§3).
2. The handover's "redo `proof_words`/`logWords_tSegs` for `reassemble4 seq4 0` and `itemsOf seq4`" is done
   parametric in `S` (decided side conditions `TrOk4`, `PfOk4`, `LadOk4`), so the rev44 port re-decides them at
   that branch's `seq4` (whose `aBytes4 ≠ 0` adds field 18: `proof_words4` is stated at `aB = 0`; rev44 needs
   the field-18 slice, one more `cpSlice4` case).

### 7. Handover: what remains, in order

1. **Chain words ↔ heap (pure).** `chW κ σ k w n := hMW w (8·blkOf κ σ k (n/8) + n % 8)`; chain byte `p <
   streamB` is byte `p mod 8` of `chW (p/8)` (`hMB_eq`, the block's `msgBytes`/`readByte`, `hMW_byte`);
   `(vS κ σ k i w)[u] = shWd chW s (q + u)` (`s > 0`) or `chW (q + u)` (`s = 0`), `q = D/8`, `s = D mod 8`,
   `D = i(segB − 1)` (`wOf_eq`, `shWd_byte` — generic in `W`). Header: `hAe` = `shWd (hMW w) 1 (8·cAB + j)`,
   `j < 4`; `hAn` = `shWd (hMW w) 1 (8·cAB + 4)` (`hA` is the `cAB` block's message bytes 0–40).
2. **`FRXOut4R`, the programs** (all new code; `FRXOut` is done):
   - the H loader `apH κ := ⟨3, 3, 2, mLog 0 + 1⟩` at `R = map4.l0.ob + 3·2^(mLog 0 + 1)` (`addrW apH R n =
     hAddr κ n`, `hAddr_eq`);
   - `finCopy`: 8 load/store pairs from `8·finBlk κ σ k + j` to `8·(chBase κ σ + aggL k − 1) + j` (`k` in a register);
   - the realign loop (`loopK` over `segB/8` words; `D = i·(segB − 1)` by `mul`, `q = D >>> 3`, `a = (D & 7) <<< 3`,
     `b = 63 − a`; word `(H(n) >>> a) + ((H(n+1) <<< 1) <<< b)` stored at `buf + u`): proof with `ldw_sem` and a
     custom invariant (heap outside the buffer kept), not `Ctx`;
   - emission: `Ctx M₁ buf κ` and `segIR ⟨0,1,1,0⟩ 0` of `catL (fSeg4 seq4 m f, f < 17)` once and `fSeg4 seq4 m 17`
     three times (`ite` on `b = 0x50`, `b ∈ {0x4B, 0x4D}`, `b` = buffer word 10's low byte; `mOfB`), `trSeg4`/`trBody4`;
   - aggregates: `k = kSel` (per `i < maxK`: XOR of the three selector cells' words, compare with `(1, 0)`;
     `kSel_eq`), length word `48 + k·piSize` (`mul`), `hdrWords`, loop `i < k` (`loopK` with the count register `k`,
     cap `maxK`) over realign + proof, count word `k·8905`, loop over realign + trace body;
   - the signature: two loops over `sigWords_sigH`'s shifted pairs; the statements: 4 loads each at `wAddr κ (stC κ σ h) + j`.
   Size estimate from §4's measurement: ≈ 13·10³ statements a child, ≈ 8·10⁴ for the three kinds, with the
   decoders ≈ 2.5·10⁵ ≤ `2^19`; cost ≈ 3·10⁷ a segment (far inside `decBudget4`); output ≤ 2.3·10⁶ ≤ `outCap`.
3. **`outIR4_sem`**: from `decF04_wF`'s conclusion, `outIR4 κ` appends `witWords (readW4 sigH κ L es)`
   (`witWords_readW4`, `signedWords_prev`/`_agg` with `V i u` the buffer's words, `sigWords_sigH`, `hMW_heap`);
   `wf`, `outs`, cost bound, `sizeIR` (component lemmas, not one `decide`).
4. **`FRXNd4`**: `nd := ndK4 (.seq (decF04 .N2) (outIR4 .N2)) …`; `decOk4_nd`; `nodeDec4_nd := ⟨LinksD4, readW4 sigH,
   out⟩` (`out` from `ndK4_sem`, `decF04_sem`, `outIR4_sem`, `readW4_fits`).
5. **The plug (coordinator's ruling, 2026-10-29):** `FRSubmission4`: `ext := ext4With nd`, `E := E4X nd sub0.acc`;
   `FRSubmission4Cert`: `Open4 := gap ∧ dec` with `dec : Links4 nd nodeDec4_nd` (the `∃ D` goes),
   `certificate_sub4` with `decOk4_nd`; new **`FRSubmission4Fin`** (imports `FRXNd4`, `FRNodeLinks4SigH`):
   `Open4F := Gaps4`, `certificate_sub4F : Open4F → Certificate sub4` via `⟨h, links4_sigH nodeDec4_nd (fun _ _ _ _ _
   h => h) rfl h⟩`; `Solution.lean` imports it and `certified` takes `Open4F`.
6. Part 30 §6 item 4 (`tgBody_sem` split, reflow), unchanged.

### 8. What `Open4` still assumes (exact; unchanged by this pass)

1. `gap : Gaps4` — `∀ vk κ w c₁ c₂, StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w → Gap4R implB (fun _ => implB) pf4
   κ vk c₁ c₂ w`.
2. `dec : ∃ D : NodeDec4 ndNone, Links4 ndNone D` — unsatisfiable while `nd` is missing. After items 4–5 it goes:
   S-L4's `links4_sigH` discharges `Links4 nd nodeDec4_nd` from `Gaps4`, so `Open4F = Gaps4` alone.

### 9. Open questions

- **Q1 (orchestrator).** Accept §6.1 (realign buffer + copy instead of shift/redirect registers in `AP`)?
  The pass-8 ruling's goal — `segIR_sem` carried over, 3.x's statements true at their instances — holds
  with fewer edits to 3.x.

## Part 34 (track S-H4, pass 10): the chain words and the realign loop (items 1 and 2's core); handover for the emitters, `outIR4_sem`, `FRXNd4` and the plug

**Status.** HEAD `1f400d9` (pass 9 = `8e88890`), build tree `logs/fr-build-SH4i` (copy of `fr-build-SH4h`,
`snap.sh` on HEAD; `MINE` = pass 9's + `FRXOut4C`), logs `logs/S-H4i/`. Nothing committed. **Done: item 1
and the machine core of item 2** (the chain loader with the `finBlk` redirect in registers, and the realign
loop into the buffer, proved). **Not done: the emitters (signature, ladder, `kSel`, header, child and node
programs), `outIR4_sem`, `FRXNd4`, the plug.** `Open4`, `certificate_sub4`, `certified` unchanged; the
entry stays PROVISIONAL. §6 is the handover.

### 1. Files (`loc.py`: total / blank / comment / code / theorems)

| File | loc | Content |
|---|---|---|
| `FRXOut4C` (new) | 133 / 22 / 26 / 85 / 11 | **`chW`**; `shWd_zero`, **`wOf_shift`** (any `s < 8`), `streamBytes_getD'`, **`chainBytes4_getD`**, `getD_packBytes`, **`vS_get`**, `hA_getD`, **`hAe_words`**, `ofLE_append'`, `ofLE_range8`, **`hAn_word`**. |
| `FRXOut4R` (new) | 532 / 55 / 48 / 429 / 27 | registers `qN … qM` (100–120, below `FRXOut`'s); `apH κ = ⟨3,3,2,mLog 0 + 1⟩`, `hBase κ`, `apB = ⟨3,3,2,20⟩`, `bufB = 2^27`, `nW = 185,344`, `bufA`; **`ldC κ`**, **`rlBody κ`**, **`realign κ`**; `addrH_toNat` (any `st ≤ 20`), **`hAddr_apH`**, `bufA_apB`, `hAddr_lt`, `regs_hAddr`, `bufA_inj`, `bufA_ge/lt`; **`OF`** (the output phase's frame: heap below `bufB` kept), `of_loK`, `of_decS`, `of_entryK`; `ldIx`, `eq_toWord`, `ite_mul_toWord`, **`ldC_sem`**, `wf_ldC`, `loK_ldC`, `keep_ldC`, `ldPs_oAd`, `ldPs_keep`; **`RlInv`**, `shl_shl_one`, `shr_8s`, **`rlBody_step`**, `rlInv_entryK`, `wf_rlBody`, `wf_realign`, **`realign_sem`**. |

New code: 514 lines; neither module is in the certificate's closure yet (nothing imports them).

### 2. What is proved

- **`vS_get`** (with `hD : i(segB − 1) + segB ≤ streamB κ σ k`): `(vS κ σ k i w)[u] = shWd (chW κ σ k w) (D mod 8)
  (⌊D/8⌋ + u)`, `D = i(segB − 1)`, `chW κ σ k w n = hMW w (8·blkOf κ σ k ⌊n/8⌋ + n mod 8)`; at `s = 0` the pair is
  the word (`shWd_zero`). Via **`chainBytes4_getD`**: chain byte `p` is byte `p mod 8` of `chW ⌊p/8⌋`.
- **`hAe_words`**: `packBytes (hAe κ a w) = [shWd (hMW w) 1 (8·c_A + j)]_{j<4}`; **`hAn_word`**: `toWord (hAn κ a w) =
  shWd (hMW w) 1 (8·c_A + 4)` (`c_A = cAB κ a`). With `aggHdr_words` the header is `toWord (0x41 + 256k)` and five
  shift-1 pairs.
- **`ldC_sem`**: with `oR = hBase κ`, `qM = n`, `qCB = cb`, `qJ = jL`, `qDl = Δ`, the loader leaves in `oX` the heap
  word at `hAddr κ (ldIx cb jL Δ n)`, `ldIx cb jL Δ n = n + cb + [⌊n/8⌋ = jL]·Δ` (**the `finBlk` redirect is a
  register product, not a copy**: H is never written).
- **`realign_sem`** (`OF M₀ s`, `i ≤ 4`, `qI = i`, bounds, `hlow`: every loaded H word lies below `bufB`): after
  `realign κ`, `OF M₀` holds (the heap below the buffer is `M₀`'s), the output is unchanged, and for every `u < nW`
  the buffer word at `bufA u` is `shWd (fun n => rd M₀ (hAddr κ (ldIx cb jL Δ n))) (D mod 8) (⌊D/8⌋ + u)`. The loop
  body computes `(C n >>> 8s) + ((C (n+1) <<< 1) <<< (63 − 8s))` (`shl_shl_one`: `= C (n+1) <<< (64 − 8s)`, `0` at
  `s = 0`) and stores it with the guarded store (`rd_storeM`); `RlInv` is the loop invariant (`rlBody_step`).

### 3. Statement changes

None. `Open4`, `certificate_sub4`, `certified`, every pass-9 statement unchanged.

### 4. Deviation from the ruling (the copy)

The accepted ruling had **`finCopy`** (copy `finBlk`'s 8 message words onto the main chain's last block, in H).
This pass **redirects in the loader instead**: `ldIx` adds `Δ = 8·(finBlk − chBase − jL)` to the H word index when
the chain word's block is the stream's last (`jL = streamL − 1`), from registers. Same effect on the realigned
words; the heap below the buffer is never written, so one frame (`OF`: heap below `bufB` = the decode's) serves the
whole output (no per-child "copied block" exception), and `Δ = 0` for a previous node and for `k = maxK`
(`finBlk = chBase + chLen − 1 = chBase + jL`), so one loader serves every child. The realign into the buffer and
`segIR` over `apB` are as ruled.

### 5. Controls and checks (logs in `logs/S-H4i/`)

- Controls: none new yet (the pieces are universal lemmas; the negative controls belong with the programs:
  §6 lists them).
- **Build:** `lake build FR Solution FRSubmission4Cert FRXOut4R` green on HEAD `1f400d9`, **2,614 jobs**
  (`build2.log`; on the old HEAD `91d74b0` + pass 9: `build1.log`, 2,611; baseline `build0.log`, 2,609).
- **Axioms** (`axioms.log`, `logs/fr-build-SH4i/ax/AxSH4i.lean`, 11 declarations incl. **`certificate_sub4`**,
  **`RecursionFast.Challenge.certified`**, `vS_get`, `hAn_word`, `ldC_sem`, `rlBody_step`, `realign_sem`): within
  `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- **Source rule** (`source-rule.log`): 389 files, 0 findings.
- Elaboration (`lake env lean`, one module): `FRXOut4R` ≈ 8 s wall; `FRXOut4C` ≈ 6 s.

### 6. Handover: what remains, in order (design fixed by this pass)

Registers `qN … qM` (100–120) are below `FRXOut`'s (200–255), so `segIR` keeps them (`frame` + `wrL`).
`apH κ`/`hBase κ` read H (`hAddr_apH`); `apB`/`bufB` read the buffer (`bufA_apB`). Every emitter after the decode
runs under `OF M₀` with `M₀` the heap after `decF04 κ` (`hMW_heap` gives `rd M₀ (hAddr κ n) = hMW (wF κ L es) n`,
`decF04_wF` the statement and selector cells).

1. **Chain registers for child `σ` with `k` segments** (static for a previous node: `cb = 8·chBase κ 0`,
   `jL = cLen − 1`, `Δ = 0`; at run time for aggregate `a`, `σ = aggChild κ a`): `qCB := 8·chBase κ σ`,
   `qJ := (qK·(segB − 1)) >>> 6` (`= aggL k − 1`), `qDl := [qK <ᵤ maxK]·8·(finB κ a + qK − 1 − chBase κ σ − qJ)`.
   Pure lemma: for `n/8 ≤ jL`, `ldIx cb jL Δ n = 8·blkOf κ σ k (n/8) + n mod 8`, hence `rd M₀ (hAddr κ (ldIx …)) =
   chW κ σ k (wF) n`; a `shWd_congr` (agreement on `n`, and on `n + 1` when `s ≠ 0`) then turns `realign_sem`'s
   buffer into `(vS κ σ k i (wF))[u]` (`vS_get`). `hlow` from `hAddr_lt` (all blocks `< hEnd κ`, per-kind numerals).
2. **Emitters** (new, `FRXOut4R` or a sibling `FRXOut4E`):
   - `shwIR ap s` (two `ldw`, shifts `8s` / `64 − 8s`, `out`): `shWd (src M₀ ap R) s n`, the pattern of `segIR`'s
     `.shw` case generalised to `0 < s < 8` (shift 3 is needed by the chain values).
   - `sigIR κ σ`: the index (`shwIR 1` at `8·wb 399`, kept in a register), `loopK` over 133 chains (four `shwIR 3`
     from `qP`, `qP += 24`), `loopK` over 16 levels (bit `(idx >>> t) & 1`, base `qP + 4 − 4·bit`, four `shwIR 1`,
     `qP += 16`): `= sigWords (sigH κ σ w)` by `sigWords_sigH` and `toWord idx = shWd …` (its `e1`).
   - `pfIR`: `segIR apB 0` over `catL ((range 17).map (fSeg4 seq4 32))`, then buffer word 10 `&&& 255` and the ladder
     `ite (= 0x50) (field 17 at 30) (ite (= 0x4B ∨ = 0x4D) (… 31) (… 32))`. Pure lemmas: `fSeg4 S m f = fSeg4 S 32 f`
     for `f ≠ fSibs` (induction on `pRest4`), `segOut` of `catL` = flatMap, `mOfB b = if b = 0x50 then 30 else if b =
     0x4B ∨ b = 0x4D then 31 else 32` (`decide` over `UInt8`). `okSeg`/`depthSeg` of the four segments by
     `decide +kernel` (pass 9's scratch: all hold, depth 1).
   - `kSelIR κ a`: per `i < maxK` (unrolled) XOR the three selector cells' two words (F addition is
     coefficientwise XOR, `FRField128.add`), flag `= (1, 0)`, `alive &&= flag`, `qK += alive`; pure lemma: that sum
     is `kSel` (`find_range_getD`).
   - statements: per cell two loads at `wAddr κ (stC κ σ h)` (`elemWords_rdF`, `out_cells_dec0`, `decF04_wF`).
3. **Children and `outIR4 κ`**: prev = `|π|`, realign `i = 0`, `pfIR`, `segIR apB 0 (trSeg4 seq4)`, `sigIR`;
   aggregate = `kSelIR`, `48 + k·piSize`, `hdrWords` (`0x41 + 256k`, then `shwIR 1` at `8·c_A + 4` and `+ j`),
   `loopK qSc qK maxK (realign; pfIR; qI += 1)`, `k·|items|`, `loopK (realign; segIR (trBody4 seq4); qI += 1)`,
   `sigIR`. `loopK` with a run-time count `k ≤ K` needs an `entryK` lemma for `rd n = toWord k`, `k ≤ K` (the count
   is `min`: `entryK`'s `ltu` branch), and `loopK_emit` re-stated for it. `outIR4 κ` = tag `1`, the four statement
   cells, child 0 (prev for `N2`/`N4`, aggregate 0 for `N8`), child 1 (the aggregate). `outIR4_sem` composes
   `signedWords_prev`/`_agg` (with `V i u := rd M_i (bufA u)`), `witWords_readW4`.
4. Cost/outs/size/wf: every piece is `NoLoopT`; cost is an upper bound only (`DecOk4.cost` has
   `decBudget4 − cost_le_decF04 ≈ 1.03·10^14` free; the output is `≈ 10^8`): `realign` = `8 + nW·(cost rlBody + 3)`
   (`rlBody` ≈ 70 steps), segments by `decide +kernel` on `cost (segIR apB 0 seg) 0`. Sizes by `decide +kernel`
   per segment (pass 9: 4,940 + 3·1,245 + 4,904 per child).
5. `FRXNd4`, the plug, `FRSubmission4Fin`, `Solution` (Part 33 §7 items 4–5, unchanged), then item 6.

### 7. Open questions

- **Q1 (orchestrator).** Accept §4 (loader redirect `ldIx` in registers instead of `finCopy`)? It keeps H
  unwritten and needs no per-child heap exception; the ruling's buffer and `segIR` are unchanged.
