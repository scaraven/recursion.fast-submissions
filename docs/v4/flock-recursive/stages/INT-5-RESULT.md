# INT-5 RESULT: revision 3.16 in S-0, S-C, S-F2 (R-V-M1, R-V-M2, R-V-m1) (2026-10-28)

HEAD `f9e2afc` (the 3.16 blueprint) at the start, `feca303` at the end (§7). Build tree `logs/fr-build-INT5` (INT-4's copied; `snap.sh`:
HEAD's sources, this pass's modules symlinked to the worktree). Logs in `logs/INT-5/`. Journal:
`INT-5-JOURNAL.md`. Every lean/lake command ran in the 16G scope with a `timeout`. Nothing is
committed. S-E10's and S-G7's in-progress files were not touched (the HEAD snapshot excludes them).

**State: `lake build FR` is green on HEAD `feca303`, 2,397 jobs** (`build-FR-3.log`; on `f9e2afc`: 2,389 jobs, `build-FR-2.log`). The axioms are clean
(`axioms.log` on `f9e2afc`, `axioms-feca303.log` on `feca303`: 40 names) and the source rule passes
(`source-rule.log`: 173 files; `source-rule-feca303.log`: 176 files; 0 findings).

## 1. What changed, by module (code lines from `loc.py`, HEAD → INT-5)

| Module (owner) | Change | Code |
|---|---|---|
| `FRVIR` (S-0) | `Op.rsWeight r pts κ β act ρ` (β, and `1` where `act` fails); `OpImpl.rsWeight … κ β ρ`; `Meets`: the rsWeight conjunct gains β and `23 ≤ ρ.size`; **`Val.isBit`**, **`assertBit`** in `evalOp`; **`nodeKindW`**; controls `maskOf_pos` (rewritten), `maskOf_free_old`, `isBit_pos/neg`, **`assertBit_rejects`**, `assertBit_accepts`; `kindFoldWeight` documented as withdrawn | 586 → 606 |
| `FRVIRFinals` (S-0) | run kit moved here (`pureRun_append` from SF, `pureRun_rebase` from SG; new `pureRun_seq`); **`dotOps`/`dotVals`/`dotAcc`, `run_dotOps`, `dotOps_noAsk`, `dotAcc_eq`**; **`finLc` = `lcHead ++ dotOps … 64 ++ lcTail`**; **`relLc`** restated (`lcV`, `lcRhi`, `lcRk`, `lcWalk`, `lcVf`, `lcFree`); **`flag_finLc`** re-proved; control `lcFree_leaf` | 346 → 543 |
| `FRVIRFinalsSF` (S-F) | `pureRun_append` moved out (same statement) | 521 → 508 |
| `FRVIRFinalsSG` (S-G's field, S-0 module group) | `finPf`'s `rsWeight` passes L3β's `β` and `Kind.isNode`; `w0V`; `pfRefs` (+ L3β's `β`); `flag_finPf` proof repair; `pureRun_rebase` moved out | 1,501 → 1,493 |
| `FRRingSwitch` (S-C) | **`rsWeight_kind_eq`** (+ `hiIdx`, `hiIdx_join`, `kindFac`, `kindFac_frob`) | 500 → 542 |
| `FRSpartan` (S-C) | **`linM_free_mle`** | 415 → 433 |
| **`FRKindWeight`** (new; S-C spec + S-F2 impl) | `kwS` (spec), `kwI`/`kwCore` (impl), **`kwI_eq`**, `pfx_eq`, `item_val`, `planFix_ivs`, **`part_one`**, **`kwS_one`**, controls `kwS_cube`, **`kwS_hashA`**, **`kwS_hashA_ne_plain`** | 405 (new) |
| `FRVerifierImplOps` (S-F2) | **`rsWeightI`/`rsWeightS`** with β (claim 2 kind-weighted: `wEvalKC`, `kwSL`), `wEvalKC_fold`, `wEvalKC_eq`, **`rsWeight_meets`** | 457 → 507 |
| `FRVerifierImpl` (S-F2) | `implCWith_meets`' rsWeight case (two more binders); docstring | 95 → 95 |
| `FRVIRCompile` (L-circ) | `opOut (.assertBit ..)`: `foreign := true` (one line; §4 D3) | 845 → 846 |
| `FRSoundnessAccLog` (S-G) | proof repairs `noAsk_finLc`, `pfRefs_lt` (§4 D4) | 440 → 442 |
| `FR` | `import FRKindWeight` | — |

## 2. Item 1: R-V-M1, ruling (a) — `rsWeight`'s claim-2 kind factor

**S-C, `FRRingSwitch.rsWeight_kind_eq`** (kernel-checked, generic over a characteristic-two ring):

```
mle (fun y ↦ Phi fs (eq (Fin.append p₁ p₂) (cube y) * kindFac Ind β (hiIdx y))) (Fin.append ρ₁ ρ₂) =
  ∑ k ∈ range (2 ^ fs.length), (phiTable fs).getD k 0 * ∑ κ, β ^ (κ.val * 2 ^ k) *
    eq (fun l ↦ p₁ l ^ 2 ^ k) ρ₁ * ∑ t, Ind κ t * eq (fun l ↦ p₂ l ^ 2 ^ k) (cube t) * eq ρ₂ (cube t)
```

for 0/1 indicators `Ind` (`kindFac Ind β t = Σ_κ β^κ Ind κ t`). Disjointness is not needed
(Frobenius is additive: `kindFac_frob`). This is A.8's formula with `p₁ = p_hi` (7), `p₂ = p_blk`.

**The layout instance (`FRKindWeight`).**
- `kwS n β q ρ = Σ_{i<8} β^i Σ_{t<2^n} selOf(ivsQ n κ_i)(t)·eq(q,t)·eq(ρ,t)`, `κ_i` = `blockKinds.tail`
  (`finLc`'s `v_i` order), `ivsQ` = `Layout.kindIvs` with `free` extended to `[wmBase, 2^n)`.
- `kwI` computes it from per-bit tables (`e1 = qρ`, `e0 = 1−q−ρ+e1`, prefix products), prefix sums
  high bit first (`pfx`, one product per bit) and **23 items** (`plan`): `stream` 4 intervals,
  `streamStart`/`streamEnd41`/`hashA` 2 single blocks each, `hashB1` 4 singles + 2 even patterns,
  `hashB2` 2 singles + 2 odd patterns (the path runs `[W_σ+466, W_σ+498)` as bit 0's weight times a
  15-bit range sum), `w43` 2 intervals, `free` 1 interval.
- **`kwI_eq`**: `kwI n β q ρ = kwS n β q ρ` for `n ≥ 16`. `planFix_ivs` checks the items against
  `Layout.kindIvs` (kernel `decide` on the concrete lists).

**Leaves: the factor is trivial, exactly because `β = 1`.** The op gates β: `evalOp` passes
`if act κ then β else 1`, and `gen` passes `act = isNode` (dump: `rsWeight … r796 true` on N,
`… r796 false` on L, P). With `β = 1`, `kwS n 1 q ρ = eq(q, ρ)` (**`kwS_one`**, `n ≥ 16`), because
the kinds partition `[0, 2^n)` (**`part_one`**: the seven non-free kinds' intervals are a
permutation of `nodeLayout` below `wmBase`, chained from 0 to `wmBase` — both `decide +kernel` —
and `free` is the rest). So a leaf's claim-2 weight is `Σ_k c_k eq(p_hi^{2^k},ρ_hi)·eq(p_blk^{2^k},
ρ_blk)` = the 3.15 plain weight; L32's 18 block coordinates are covered (`free` up to `2^18`).

**S-F2.** `rsWeightS` (spec) = 3.15's for claims `j ≠ 1`; claim 1 (RS claim 2) is
`Σ_k c_k·kwSL(β^{2^k}, r_1^{2^k}, ρ)`, `kwSL = eqPts(q[0..7), ρ[0..7))·kwS(|ρ|−7, …)`.
`rsWeightI` folds the stages (`wEvalKC`). **`rsWeight_meets`**: equal for `r″` of 7 and
`23 ≤ |ρ|`. `implC_meets` re-proved (text unchanged).

**Controls.** `kwS_cube`: at a Boolean point the factor is `Σ_i β^i Ind_{κ_i}(t₀)`.
**`kwS_hashA` (+)**: at `hashStmt` block A it is `β^3`. **`kwS_hashA_ne_plain` (−)**: at `β = 0` it
is `0`, while the 3.15 plain weight is `1` (R-V-M1's defect, on one block).

**The op's cost (measured).** `vtime ops`: `rsWeight` (4 claims) 40.3 ms (INT-4: 7.2 ms);
`KW.kwI` ×128 alone 46.9 ms. The impl does ≈ 640 K×K products per stage (setup 78, the items'
prefix sums ≈ 350, single blocks 12 × 16, β powers, sums), ≈ 82 k per call — the blueprint's
count (≈ 68 k) — but **a K product costs ≈ 0.45 µs** (INT-4's `mulK`: 16,406 ops in 8.2 ms), not
the ≈ 90 ns the blueprint's "+6 ms" assumes: **+33 ms VM, not +6 ms**. Levers (not taken; §6):
endpoint sharing across items (≈ 21 distinct endpoints + 4 half-width, ≈ −20 %), the `q` side in F
(the claim points are F values; `q·ρ` as `smulF`).

## 3. Item 2: R-V-M2 — `free` off the walk; the closed-form `free` term

**The ops** (`finLc fi b`, N30 dump lines 66,107–66,397):
- `lcHead`: as 3.15 up to the walk (`b … b + 22`), `hornerOps`, (iii)'s assert, then `keep isNode v₇
  0` (`b + 37`), `eqZ λ 0` (`b + 38`: `L_s(λ)` for `s < 64`), `packF r_k[0..5]`, `eqTable` (`b + 40`).
  **The node's `packFK` is `nodeKindW`: `[0, v₀ … v₆, 0]`** (entry 8, `free`, is the zero register
  `b + 14`; dump line 66,108). The leaf's `[v₀, 0^8]` is unchanged.
- `dotOps (b+38) (b+40) (b+14) (b+41) 64`: per `s`, `getF`, `getF`, `mulF`, `addF` into the running
  sum (from the zero register); the sum `Σ_{s<64} L_s(λ) eq(r_k[0..5], s)` at `b + 296`.
- `lcTail`: `packF r_k[6..13]`, `eqPt r′_hi r_k[6..13]`, `X = sum·eq`, `Y = v_free·X`, `αY`,
  `Y + αY`, `walk + (Y + αY)`, **`assertEq … claimN(L2)`** — (ii) now closes `finLc`.
- Exports `[b + 36]` (`v_β`) as before. Registers `b … b + 36` are unchanged.

**`relLc`** (statement change, 3.16): `((i) && (iii)) && (ii)` with
(ii) `c_Lc = lcWalk + (Y + αY)`, `lcWalk` = the walk at `maskRows (nodeKindW v | v₀::0^8) rowW`,
`Y = lcFree = v_free·(dotAcc 0 (eqZ λ 0) (eqTab r_k[0..5]) 64·eqPoint(r′_hi, r_k[6..13]))`,
`v_free` = a node's `v₇`, a leaf's `0` (`lcFree_leaf`: a leaf's (ii) is the 3.15 one).
**`flag_finLc`**: same text and `hin`; proved in three blocks (`pureRun_seq`, `run_dotOps`).

**S-C spec of (ii)'s term.** **`linM_free_mle`**: `mle (linM I I (rowW λ r′_hi) α) (r₁, r₂) =
(1 + α)·(Σ_{s<64} L_s(λ) eq(r₁, s))·eq(r′_hi, r₂)` — `linM_free` (`A₀ = B₀ = I`) in the closed form
`finLc` computes; with `lin_final_kinds` it is the `free` summand of the true L2 value. `dotAcc_eq`
reads `dotAcc` as the finite sum.

**Controls.** **`maskOf_pos` (+)** now runs `maskOf` on `nodeKindW` with `v_i = 2^(i+1)`: row 0's
mask is `2 + 8 + 64` (no `free`), past `pinEnd` 254. **`maskOf_free_old` (−)** (the former
`maskOf_pos`): the 3.15 vector puts `free`'s weight 256 into row 0.

## 4. Item 3: R-V-m1 — `assertBit`

`evalOp (.assertBit a act) = .vals [] (!act κ || (rd regs a).isBit)`, `isBit` true on `.bit _` and
the F values 0, 1. Unused by `gen` (count 0 in every dump). Controls **`assertBit_rejects` (−)**
(F value 2, active: `ok = false`), `assertBit_accepts` (+: F 1; inactive), `isBit_pos/neg`.

## 5. Deviations and statement changes (for the orchestrator)

**D1. β is gated inside `rsWeight` (`act` operand), not a `finLc` export.** A leaf must pass
`β = 1`. A register computed in a final field and read by `finPf` would make S-G's `pfRefs_lt`
("`finPf` reads only the skeleton's registers") false. So the op takes `β` (L3β's, a skeleton
register) and `act : KC Bool`, and uses `1` where `act` fails. The op stays kind-free in its
arithmetic; the gate is a mux, as `keep`. A.8's row needs the operand: `rsWeight r″ pts κ β act ρ`.

**D2. `kindFoldWeight` stays as a dead constructor** (`implC`: 0). Removing it edits L-circ
(`FRVIRTplExt` cases on it; S-E10 has that file open).

**D3. L-circ edit (forced by m1): `FRVIRCompile.opOut (.assertBit ..)` is `foreign := true`**
(was `{ slots := [] }`). `opOut_sound` needs a non-foreign op's flag implied by its rows; an
implemented `assertBit` has no rows, so it must be foreign (or be arithmetised: S-E). `gen` emits
none, so no compiled circuit changes.

**D4. S-G proof repairs (statements unchanged)**, `FRSoundnessAccLog`: `noAsk_finLc` (plain `simp`
timed out unfolding the 64-term block; now `dotOps_noAsk` first), `pfRefs_lt` (one case: L3β's β).
No S-G7 file was touched.

**D5. Statement / definition changes, each from 3.16:**
- `Op.rsWeight` (β, act), `OpImpl.rsWeight` (β), **`OpImpl.Meets`' rsWeight conjunct** (β;
  precondition `r.size = 7 → 23 ≤ ρ.size`), `evalOp` (`rsWeight`'s β gate, `assertBit`).
- **`rsWeightI`, `rsWeightS`** (β; claim 2's kind factor), `rsWeight_meets` (β, `23 ≤ |ρ|`).
- `finLc` (ops), **`relLc`** (§3), `flag_finLc` (text unchanged, meaning via `relLc`).
- `finPf` (rsWeight's operands), `w0V` (β gated by `isNode`), `pfRefs` (+ L3β's β), `flag_finPf`
  (text unchanged; `hin` over the new `pfRefs`).
- `maskOf_pos` (now the 3.16 vector; the old statement is `maskOf_free_old`).
- **Unchanged in text**: `implC_meets`, `implCWith_meets`, `implCWith_implT`, `acc_eq`,
  `finalLaw_of`, `finalLaw_of_run`, `hAcc_of`, `kstate_of_front`, `flag_finZ`, `flag_finSh`, every
  S-G theorem. `pureRun_append`/`pureRun_rebase` moved with their statements.

## 6. Re-dump (`logs/INT-5/dump/`, `redump.sh`; the dump tool prints rsWeight's new operands)

- **ops 106,106** (INT-4: 105,839): **+267** = `lcHead`'s 4 (`keep`, `eqZ`, `packF`, `eqTable`) +
  256 (`dotOps`) + `lcTail`'s 7 (`packF`, `eqPt`, 3 `mulF`, 2 `addF`); (ii)'s assert moved.
- **asks = items = 8,891 (unchanged); `items.json` byte-identical to INT-4's** (sha256 `71b533a2…`);
  **piSize 797,904 (unchanged)**; no `PENDING`.
- Wiring (N30): `rsWeight r93481 [r93185 r93235 r93285 r93309] r2172 r796 true r93480`: β = `r796`
  = L3β's β, the register `hornerOps` uses for (iii) (`mulF r796 …`, lines 66,115 on); L, P: `false`.
- **Honest-value consistency** (`scripts/kindcheck.py`, `kindcheck.txt`; GF(2^8), 3 seeds, honest
  z, a 16-block layout with intervals, singles and an even/odd run): (1) `Σ_i β^i v_i = ⟨g, z⟩` with
  `g = eq(p,·)·B_β` — the value RS claim 2 now certifies, so (iii) holds; (2) the MLE of `Φ(g)` at
  ρ (brute force) equals the item algorithm of `kwCore` (`pfx`, singles, patterns); (3) R-V's
  counter-situation: the 3.15 plain weight certifies `Σ_i v_i ≠ Σ_i β^i v_i`; (4) `β = 1` gives the
  plain weight. The Lean statements behind (1)–(2): `lin_beta_claim`, `rsWeight_kind_eq`, `kwI_eq`.

## 7. V (N30), S-E8's method (`vt.sh`, core 30, 21 warm `runSeq` runs)

HEAD moved during this pass (S-G8 `62a25fb`, S-E11 `9cc1052`, S-G9 `feca303`). The changes were
re-built on `feca303` (`build-FR-3.log`: green, 2,397 jobs; no further repair needed) and V
re-measured there.

| Binary | Run | best | median |
|---|---|---|---|
| INT-5 on `f9e2afc` | `vtime-N-a` | 314.7 ms | 330.8 ms |
| INT-4 (`750ab01`), interleaved | `vtime-N-int4-a` | 219.1 ms | 235.3 ms |
| INT-5 on `f9e2afc` | `vtime-N-b` | 322.4 ms | 348.6 ms |
| INT-4 (`750ab01`), interleaved | `vtime-N-int4-b` | 216.1 ms | 226.8 ms |
| **INT-5 on `feca303`** (S-E11's evaluator) | `vtime-N-c` | **233.2 ms** | 242.4 ms |
| **INT-5 on `feca303`** | `vtime-N-d` | **226.3 ms** | 233.3 ms |

S-E11's own figure for HEAD is 192.9 ms best (commit message; not re-measured here).
**On the current HEAD, V is ≈ +33–40 ms, and `rsWeight` accounts for it:**
- **`rsWeight` 7.2 → 38–40 ms (+31–33)** (`prof-N*.log`): §2's K products.
- **`evalM` 83 ms on `feca303`** (`prof-N-c.log`; S-E11 reports 81–89): the 267 new `finLc` ops cost
  it nothing measurable there. On `f9e2afc`'s evaluator it went 110 → 193 ms (`prof-N.log`,
  `prof-N-b.log`; node plan 89 keys / 5,148 pieces per slot against 83 / 5,062), which S-E11's
  evaluator removed.
- The rest is within run-to-run spread.

## 8. Checks

- **Axioms** (`axioms.log`, 40 names): `acc_eq`, `implC_meets`, `implCWith_meets`,
  `implCWith_implT`, `finalLaw_of_run`, `finalLaw_of`, `hAcc_of`, `kstate_of_front`, `flag_finLc`,
  `flag_finZ`, `flag_finSh`, `rsWeight_kind_eq`, `kindFac_frob`, `linM_free_mle`, `kwI_eq`,
  `kwCore_eq`, `pfx_eq`, `item_val`, `part_one`, `kwS_one`, `kwS_cube`, `kwS_hashA`,
  `kwS_hashA_ne_plain`, `rsWeight_meets`, `wEvalKC_eq`, `run_dotOps`, `dotAcc_eq`, `lcFree_leaf`,
  `pureRun_seq`, `assertBit_rejects`, `assertBit_accepts`, `flag_finPf`: `propext`,
  `Classical.choice`, `Quot.sound`; `planFix_ivs`, `isBit_pos/neg`: `propext`; `dotOps_noAsk`,
  `maskOf_pos`, `maskOf_free_old`, `pfRefs_lt`, `noAsk_finLc`: `propext`, `Quot.sound`.
- **Source rule**: 173 files, 0 findings.
- **Name clashes**: every new name has one declaration in the entry, untracked files included.
- **Sequential profiles** (one core, `-DElab.async=false --profile`; `profile-<module>.log`):

| Module | wall | type checking | elaboration | max RSS |
|---|---|---|---|---|
| `FRKindWeight` | 15.5 s | 2.43 s | 0.49 s | 2.72 GB |
| `FRRingSwitch` | 15.6 s | 0.71 s | 0.77 s | 2.62 GB |
| `FRSpartan` | 18.9 s | 0.82 s | 1.24 s | 2.62 GB |
| `FRVIR` | 26.6 s | 2.37 s | 10.4 s | 2.70 GB |
| `FRVIRFinals` | 42.7 s | 2.44 s | 20.4 s | 2.79 GB |
| `FRVIRFinalsSG` | 82.4 s | 4.90 s | 31.7 s | 3.35 GB |
| `FRVerifierImplOps` | 17.9 s | 4.31 s | 0.51 s | 3.06 GB |
| `FRVerifierImpl` | 6.8 s | 0.01 s | 0.03 s | 2.75 GB |
| `FRSoundnessAccLog` | 20.8 s | 0.93 s | 0.38 s | 2.94 GB |
| `FRVIRCompile` | 36.3 s | 1.29 s | 1.35 s | 2.73 GB |

(`FRVIRFinals` was profiled with `flag_finLc` under `maxHeartbeats 1000000`; the option was then
removed: the module elaborates with the default in 40 s, and `lake build FR` was re-run.)

## 9. For P2 (`ir.rs`, the prover)

1. **`rsWeight r″ pts κ β act ρ`**: β is read from its register (`r796`, L3β's β) where `act κ`
   (N30), else `1` (L32, P30). Claim index 1 (RS claim 2, Lc) uses
   `Σ_k c_k(r″)·eq(p_hi^{2^k}, ρ_hi)·Σ_{i<8} β^{i·2^k} Σ_{t∈I_i} eq(p_blk^{2^k}, t)·eq(ρ_blk, t)`,
   `p_hi`/`ρ_hi` the first 7 coordinates, `p_blk`/`ρ_blk` the remaining `|ρ| − 7`; `I_i` the node
   kinds' blocks in `blockKinds` order after `chain` (`stream, streamStart, streamEnd41, hashA,
   hashB1, hashB2, w43, free`), `free` = `[47,294, 2^{|ρ|−7})`. `FRKindWeight.plan` lists the
   23 items; `kindcheck.py`'s `kw` is a reference port.
2. **`v_RS` and RS claim 2.** The honest `v_κ = zfold_κ(r_k)` are unchanged. RS claim 2 is now the
   weighted claim `α_Lc = ⟨W_β, z⟩ = Σ_i β^i v_i`, `W_β(t, j) = eq(r′_blk, t)·B_β(t)·eq(r_k, j)`: RS0's
   claim-2 slices are those of this claim (outer weight `eq(p, ·)·B_β`, not `eq(p, ·)`), and `T₂`,
   hence `v_RS = T₀ + κ(T₁ + κ(T₂ + κT₃))`, follow. Leaves: unchanged (`B_1 ≡ 1`).
3. **`finLc` (ii)**: the node's walk mask is `[0, v₀ … v₆, 0]`; (ii) is
   `c_Lc = walk + (1 + α)·v_free·(Σ_{s<64} L_s(λ)·eq(r_k[0..5], s))·eq(r′_hi, r_k[6..13])`,
   evaluated as `Y + αY` after the 64-term sum (`eqZ(λ, 0)[s]·eqTable(r_k[0..5])[s]`, in order from
   0). Leaves: `v_free = 0`. The ops are all existing kinds (`keep`, `eqZ`, `packF`, `eqTable`,
   `getF`, `mulF`, `addF`, `eqPt`, `assertEq`). Registers from `finLc`'s `b + 37` on are new;
   later fields move by 267.
4. **`assertBit`** checks `b ∈ {0, 1}` (F) or a `bit`, where active; `gen` emits none.

## 10. For S-E (templates, A.11)

1. **The kind-factor template** (`rsWeight`'s claim 2; an import today: `.rsWeight .. => imports
   cs [.k]`): per Frobenius stage `k`, with `q = p^{2^k}` (23 coordinates squared once per stage) and
   `β_k = β^{2^k}` (gated: `1` for a P30 child): `e1_l = q_l ρ_l`, `e0_l = 1 − q_l − ρ_l + e1_l`
   (`l < 16`), `sp_{l+1} = sp_l·(e0_l + e1_l)`, `lw_l = sp_l·e0_l`, and the shifted `sp′`, `lw′`
   over bits 1…15; per item: an interval `pfx(hi) − pfx(lo)` (`pfx`: high bit first,
   `lw_{n−1} + e1_{n−1}·pfx(x − 2^{n−1})` or `e0_{n−1}·pfx(x)`, `sp_n` at the top), a single block
   `Π_l e_{c_l}`, a pattern `e_c^0·(pfx′(b) − pfx′(a))`; then `eq(q_hi, ρ_hi)·Σ_i β_k^i V_i`. The item
   list is fixed (`plan`), so the template is regular; the endpoints are constants.
2. **The `free` term's template** (`finLc` (ii)): `keep`, `eqZ λ 0`, `packF`, `eqTable` (6
   coordinates), 64 × (`getF`, `getF`, `mulF`, `addF`), `packF`, `eqPt` (8 + 8), 3 `mulF`, 2 `addF`,
   `assertEq` — ≈ 70 product rows. With S-E11's evaluator, `evalM` is unaffected (§7).
3. **`assertBit`** is foreign in `opOut` (D3); arithmetise it (gated `b(b+1) = 0`) if `gen` ever
   emits one.

## 11. Open items

1. **V: +31–33 ms VM from `rsWeight`** (226–233 ms best on `feca303`): the K products (levers in
   §2). The 3.16 estimate (+6 ms) assumed ≈ 90 ns per product; a K product costs ≈ 0.45 µs.
2. A.8/A.9 rows: `rsWeight`'s `act` operand (D1); `finLc`'s op order (ii's assert last, §3).
3. S-G: `gL`/`trueL` with the kind factor can use `rsWeight_kind_eq` with `Ind := selOf (ivsQ …)`
   (0/1 since each kind's intervals are disjoint) and `kwS_one` for leaves; `truthLc`'s `free` term
   is `linM_free_mle`; `accept_fields` per R-V-m2 (not this pass).
4. `kindFoldWeight` removal (D2) when L-circ is free.
