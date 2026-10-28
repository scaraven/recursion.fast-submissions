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
