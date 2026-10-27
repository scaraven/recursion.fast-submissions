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
