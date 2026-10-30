# SEG-R: binding the segment program's five replay ops (`rsWeight`, `evalL`, `evalM`, `shiftTarget`, `targetS`) at prototype 1

Design memo, track SEG-R, 2026-10-30. Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD
`32e4e9c` + FOLD2 pending). Memo only: no Lean, no prover, no build, nothing committed. Read:
`QUEUE.md`; `stages/IMPC2b-RESULT.md`, `REPF-RESULT.md`, `C1-RESULT.md`, `C1b-RESULT.md`,
`R3-RESULT.md`, `R0-RESULT.md`, `R1-RESULT.md`, `INIT-RESULT.md`, `RUN1-RESULT.md`, `D1p-RESULT.md`,
`S-E14-RESULT.md`, `CF-JOURNAL.md`; `design/PACK-4.4.md` §6, §8, `RSV2.md`, `R-OPS.md`; Lean:
`FRNodeSound4` (`implP`), `FRSegTarget4` (`implSeg`, `targetSSegI`), `FRVerifierImplOps`
(`shiftTargetI`, `rsWeightF`, `kwSL`), `FRKindWeight` (`kwS_one`), `FRVerifierImplCore` (`implCN`,
`nodePlan`), `FRVIRFinals4` (`gFinE0`, `gFinPf`), `FRVIRCompile` (`imports`), `FRNodeRows4Defs`
(`rtC1c`, `KOp`, `kTpl`, `repSegB`), `FRNodeRows4` (`RepFit`), `FRNodeRows4Plan` (`repV4`),
`FRNodeRows4ArenaPlace`, `FRNodeRows4Model`, `FRVIRTplCore` (`Gate`); the dumps
`logs/RSV2/dump/group-S.txt`, `logs/RSV2/nodedump/mregs-p1.txt`, `logs/CK/arenafit.log`,
`logs/B2pp/cellfit-3.log`, `logs/IMPC2b/patch.py`.

## 0. Summary and recommendation

1. **Two of the five ops are dead and two are small; only `rsWeight` is large.** In `progSegG`
   (`group-S.txt`) `evalM` (line 65815) and `evalL` (65820) feed only an `assertEq` that is inactive
   at every kind (S-E14 §2); `targetS` (276) is `targetSSegI`, affine in one challenge times an
   18-bit range factor (≈ 140 rows); `shiftTarget` (65721) is `shiftTargetI` on the statement's two
   digests (≈ 3.1 k rows with the bit decomposition); `rsWeight` (101782) has three claims, `act`
   false at every kind (so `β = 1`) and **every claim point is an F-point** (`mulKF r92569 ·` with
   `r92569 = const K 1`, lines 101268–101446).
2. **Route: replay templates in the segment slot's own region, one `RT` per op, through a new
   generic wrapper `rtKD`** (C1's `KOp`/`rtK` plus an *input mux* over the three segment kinds and
   *forcing rows* on operand cells or decomposition locals). No format change, no challenge, no
   error row, a fixed point under recursion (§3). `evalM`/`evalL` are **pinned to zero in `implSeg`**
   and bound by S-E14's `zeroRows` (6 rows); this also lets `Impl.nodePlan`/`lPlan` (3.x's plan,
   1.6–1.9 s of every start-up, INIT §1) leave the runtime.
3. **Size (per segment slot, §4–§5): ≈ 40 k rows and ≈ 40 k cells** (F-point `rsWeight` ≈ 37 k;
   K-general fallback ≈ 45 k). The segment region has **≈ 78 k free rows in two bands once IMPC2's
   `arR2N` is cut to its used extent, and ≈ 49 k free cells in two bands**. It fits with ≈ 9 k cells
   to spare; the K-general form would not. `N_M/1.05`'s model already allots 49,000 rows per segment
   region for exactly this (`FRNodeRows4Model.segRegion`), so N8's 1.0185× is unchanged.
4. **V ≈ +55–75 ms VM** as sparse rows, once per check (shared by every segment slot and every node
   kind: prototype 1 is one program), a few ms after CF's closed forms (the segment template is the
   claim part of CF's `rsGS`). **Init ≈ +0.4 s** for the rows, **−1.6 to −1.9 s** from dropping
   `nodePlan`: net −1.3 s per start, ≈ −40 s per stream. Kernel ≈ +3–5 s. Prover: honest gate
   evaluation into the locals; the f₁ cells, the L bits and the dead cells already hold what the
   forcing rows demand.
5. Rejected: carrying the segment's operands as public cells (R1's depth-2 blocker and ≥ 210 cells
   per slot, over B′'s 169 ceiling); a reserve (the ops are products, not hypercube sums); inlining
   the ops as templated VIR ops (same rows, a 20 k-op program change); placing the rows in slot 0's
   spare region with a cross-slot link (sound, but N8 has no spare region).

## 1. The problem, the constraints, what is fixed

A segment slot `v ≥ 1` replays `protoProg 1 = progSegG` at `(implSeg impl₀).fixK .L32` (`implP`).
After REPF the residual imports of prototype 1 are the 7,426 sibling reads (IMPC2b §5, not this
track) and the registers of the five ops (`impBP (rtC1c 1)`, IMPC2b §1: 73 cells). `rtC1c 1 =
rtLinkSegW repB` covers only `linkWAll` (8 rows at `v·2^20 + repSegB`, `repSegB = 1,014,784`, room
`2^10`: `FRNodeRows4Defs`, `FRNodeRows4Fit.repConsts`).

| Constraint | Value | Source |
|---|---|---|
| V per check | ≪ 2.06 s on a 7763 (DoS cap 10·v_ref); 1.78–1.83 s VM after REPF; CF expected ≲ 0.7 | REPF §4.1, RUN1 §1 |
| start-up | paid ≈ 29× per stream; 17.3–18.3 s at REPF + INIT; sparse rows ≈ 47 ms / 100 k, keyed 85–95, closed form 0 | INIT §0, §5 |
| kernel | upper set 497.8 s of 600 (1.21×) | RUN1 §1 |
| segment region rows | prototype 1 ends at 686,079; arena rows from `arR2 = 720,896`; IMPC2's constants `arR2N 180,560` (p1 uses 135,997), `arRb 998,400`, `arNb 16,384`; link region `[2^20 − 2^15, 2^20)` | `logs/CK/arenafit.log`, `ArenaPlace`, `logs/IMPC2b/patch.py`, IMPC2b §0 |
| segment region cells | skeleton ends 277,402; arena₁ `[290,816, 387,760)`; bits `[389,120, 405,504)`; lowest template instance 441,152; top 1,046,782 | `logs/CK/arenafit.log`, `logs/B2pp/cellfit-3.log` |
| N8 | `mRowModel4 .N8 = 7,843,904` of `N_M/1.05 = 7,989,150` (1.0185×) with `segRegion = [686,080, 212,640, 32,768, 49,000]`: 49,000 rows per segment region are already reserved for `R` | `FRNodeRows4Model` |
| soundness | every route a fixed point under recursion (R1 §1); FS order untouched; `εR` unchanged | R1, R-OPS "Superseded" |

## 2. The five ops in the segment program (from `group-S.txt`, `mregs-p1.txt`)

| Op (line) | Operands (register: type; kind dependence) | Value at prototype 1 | Live? |
|---|---|---|---|
| `targetS r138 → r271` (276) | `r138 : AF37` = `packFK` of Z1's position coordinate, 18 block coordinates, then `L`'s 18 bits (`lastOuts`: `addF`/`mulF` outputs, Boolean on a run); entries 17–18 differ by kind (`r133 r135` / `r13 r13` / `r133 r13`, `r13 = const 0`) | `targetSSegI r = (targetSLeafI r).map (· * segRangeI r)` (`FRSegTarget4`); `targetSLeafI` is affine in `r[0]` (7 pinned coordinates), `segRangeI = Σ_{t ≤ L} eq(blk, t)` with `L = lastAt r 19` | **yes** (→ `lagrangeS`, 277) |
| `shiftTarget r57151 r57152 r57150 r927 → r57153` (65721) | `τ : AF18` (`packFK`; entries 16–17 differ by kind), `θ : AF10` (`packF`), `bnd : AF22` = `[piElem 0 16, 0 32, 0 49, 0 65]` (the statement's `s`, `h` as F halves) ‖ `L`'s 18 bits; `κ_s = r927 : F` | `shiftTargetI κs τ θ bnd = eq(τ, L)·digestMle(Eθ, h) + κs·digestMle(Eθ, s)`, `digestMle` a bit-sum over 256 digest bits | **yes** (`assertEq r57153 r932`, 65722) |
| `evalM r57230 r57243 → r57244..46` (65815) | — | `(implSeg implCN).evalM = TEval.evalMT nodePlan` (3.x's node plan) | **dead**: feeds `mulF`/`addF` into an `assertEq … {L:false, P:false, N:false}` (S-E14 §2) |
| `evalL r57216 r57243 → r57251..53` (65820) | — | `TEval.evalLT lPlan` | **dead** (same) |
| `rsWeight r93082 {3 claims per kind} r2355 r883 {all false} r93081 → r93083` (101782) | `r″ : AF7` (`packF`, shared), `κ : F` (`chF`, shared), `β` **unread** (`act` false ⇒ `β := 1`, `evalOp`), `ρ : AK25/23/24` (`keep` mux, untracked ⇒ per-kind forms), claims `AK25 / AK23 / AK24` = `packK` of `mulKF (const K 1) x` over **F registers** (claim 1: 7 K constants ‖ Z1's 18; claim 2: `r792 …` 7 ‖ 18; claim 3: 3 ‖ 4 zeros ‖ 18) | `rsWeightF r″ ps κ 1 ρ` (3.x, `implCWith`); with `β = 1` claim 2's kind factor is the plain `eq` (`kwS_one`, `16 ≤ |ρ| − 7` holds at 23/24/25), so the value is `Σ_j κ^j Σ_{k<128} c_k(r″)·eq(r_j^{2^k}, ρ)` for all three claims; every claim point in F ⇒ `rsWeightF`'s F fast path | **yes** (→ `addK`, 101835: `finPf`) |

The program is one op list for the three segment kinds (`segGrp`): a kind only selects which
registers a `packFK`/`keep` reads, so a per-kind template differs by a few input forms, not by shape.

## 3. Routes, and why only templates

| Route | Verdict |
|---|---|
| (a) **replay template** (C1's `KOp`/`rtK`, `RTOkW` at the slot's second assignment, `compileFromX_soundRW`) | **Adopted for all five.** Rows of P's M; at the grandparent they are part of `evalM`(P's M), which RSV2's stacked reserve binds — the same fixed point REPF's prototype-0 templates rely on. No op is added to any program, so nothing new becomes an import one level up (R1 §1.5). No challenge, no FS item, `εR` unchanged. |
| (b) reserve (a parent sumcheck proving the child's value) | Not applicable: `rsWeight` and `targetS`'s range factor are products of witness-linear factors; `shiftTarget` is a bit-sum of a witness digest. A sumcheck over `k` for `rsWeight` would still need the 128 per-stage products as rows. |
| (c) public-op carry, `V(P)` recomputes | Unsound at depth ≥ 2 (R1), and the segment's `rsWeight` alone is `7 + 1 + 50 + 150 + 2 = 210` cells per slot, `k ≤ 8` slots: over B′'s 169 ceiling (R0 §3). |
| (d) make the op computable by the compiler (inline as templated `mulK`/`mulF` ops) | Same rows, in the prototype instead of `R`; a ≈ 20 k-op program change (hints, dumps, `flag_*` lemmas over `gFinPf`). Worse than (a) in every column. |
| (e) drop the dead ops from the generator (C2) | `gFinE0 … (own := true)` emits `evalM`; `evalL` (line 346) is unconditional. A program change (re-dump, hints) for the same six rows as pinning. **Pin instead** (§4.1). |
| (f) rows in slot 0's spare region, cross-slot cells | Sound (`repMapC` may map a slot's locals anywhere disjoint from its frame; `Agree`/`SelOk` are per slot) but N8 has no spare region, so it does not solve the problem and splits the layout by kind. Rejected. |

## 4. Per op

### 4.1 `evalM`, `evalL`: pin to zero, six zero rows

- **Change.** `implSeg impl₀` (`FRSegTarget4`) gains `evalM := fun _ _ => (0,0,0)`, `evalL := fun _ _
  => (0,0,0)`; `specSeg` likewise; `implSeg_meets` gains two `rfl` conjuncts. `implB` (`FRSubmission4V`,
  `= Impl.implCN = implCWith nodePlan lPlan`) becomes a plan-free copy `implC0` (same fields, zero
  `evalM`/`evalL`) so that `nodePlan`/`lPlan` are no longer referenced by any top-level constant
  (INIT rule 1: a referenced `def` is initialised at every start). Nodes are unaffected: `implN4F`
  overrides both fields (`FRVerifierImplNode4F`).
- **Rows.** `rtEvZ`: for `.evalM`/`.evalL` at prototype 1, S-E14's `zeroRows` (`one · out_j = 0`),
  3 + 3 rows, no locals. `RTOkW` holds with **no hypothesis** (the pinned implementation is the
  value), unlike `rtLinkSegW` (which needs `LinkZero`).
- **Precondition to verify (R1's first task).** No segment-side theorem reads `spec.evalM`/`spec.evalL`:
  the E asserts (`b + 8`, `b + 16`, `b + 35`) are gated by `node` (`gFinE0`'s `act`), the segment's
  lincheck goes through `rsWeight`'s claim 2 (S-F4), and `R4FrE`'s `hM`/`hL` are node-only. Grep
  `FRSoundness4XRun`, `R4FrE`, `P4aSeg`, `FRSegment`. If something does read them, fall back to (e).
- **Cost.** V: − the 3.x `evalMT nodePlan` call per segment check (measure with `vtime4 prof`); init
  −1.6 to −1.9 s (`nodePlan`, INIT §1) − 30–80 ms (`lPlan`). Kernel ≈ 0. Prover: write `0` in the six
  cells (`r57244..46`, `r57251..53`; E1 currently writes whatever `ir.rs` computes there).

### 4.2 `targetS` (`targetSSegI`): ≈ 140 rows

- **Template.** Inputs `r[0]`, `blk = r[1..18]`, `b = r[19..36]`. `targetSLeafI r` is 64 affine forms
  in `r[0]` (the eq table over `zLo r` has 7 pinned coordinates): **0 gates**. In characteristic 2 an
  eq coordinate `b_l r_l + (1 − b_l)(1 − r_l) = 1 + b_l + r_l` is linear, so `segRangeI` as a
  polynomial in Boolean `b` is `Π_j m_j + Σ_l b_l (1 + r_l) Π_{j>l} m_j` with `m_j = 1 + b_j + r_j`:
  17 suffix products + 36 products ≈ 53 gates; 64 output products `leaf_σ · range`. Kind mux on
  entries 17–18 (6 gates). ≈ 125 gates, ≈ 125 locals.
- **Forcing rows.** `b_l · b_l = b_l` on the 18 operand cells (`lastAt` reads `= 1`, not a
  polynomial): 18 rows, no locals. Honest values are bits (`selectHalf` of `bitOf`, then `addF`/`mulF`
  of bits), so the rows hold.
- **Proof.** `tplTSS_ok`: under the Boolean hypothesis, the polynomial equals `segRangeS r` (`segRangeI_eq`,
  `range_cube`'s shape; an 18-step induction on `lastAt`), times `targetSLeafI` (`targetSLeaf_meets`).
- **V/init.** Negligible. Prover: 125 locals.

### 4.3 `shiftTarget` (`shiftTargetI`): ≈ 3.1 k rows

- **Template.** `Eθ = eqTable (ptA 10 θ)`: a doubling tree, `Σ_{i=2}^{10} 2^i = 2,044` products.
  `digestMle Eθ e₀ e₁ = Σ_{σ<256} bit_σ · Eθ[σ]`: 256 `mulAdd` per digest, 512. `prodTo 18` of linear
  factors (`1 + τ_l + b_l`): 17 products. Final `mul` + `mulAdd` (`κ_s ·`). Kind mux on `τ`'s entries
  16–17 (6 gates). ≈ 2,580 gates.
- **Decomposition locals.** The 512 digest bits as locals with forcing rows: `bit · bit = bit` (512)
  and, per F half, one linear row `one · Σ_b bit_b · x^b = e` (the GF(2) basis `x^b = F.ofBytes (2^b)`;
  F addition is XOR, so the sum is `F.ofBytes (natLE bits)`). Uniqueness: `F.eq_of_bit`/`F.bit_ofBytes`
  (IMPC2b's `FRNodeRun4BL`) give `bit_b = e.testBit b`, i.e. `digBit e₀ e₁ σ`. No new `Gate`
  constructor: the wrapper `rtKD` (§4.5) emits these rows and feeds the bit cells to the template as
  extra inputs. The statement's bits already exist as arena cells (IMPC2b's `StmtBits`), but an `RT`
  sees only operand forms, so re-decomposing (516 rows) is the cheap, self-contained choice.
- **Proof.** `tplSTS_ok`: gate for gate `shiftTargetI` with the bits as inputs (`digestMle` as a
  linear form in the bits; `eqTable` tree lemmas exist from C1's `tplLW`, `eqTblG`).
- ≈ 3.1 k rows, ≈ 3.1 k locals. V/init negligible. Prover: the bits of `s`, `h` (it has them).

### 4.4 `rsWeight` (three F-point claims, `β = 1`): ≈ 37 k rows

- **Value lemma** `rsWeightF_seg : rsWeightF r″ ps κ 1 ρ = rsPlain r″ ps κ ρ := Σ_j κ^j Σ_{k<128}
  c_k(r″) · eqPtsC (r_j.map (sqIter k)) ρ` for `|r″| = 7`, `23 ≤ |ρ|`, every `r_j` an F-point:
  `rsWeightF_eq` + `rsWeight_meets` (3.x) give `rsWeightS`; `kwSL 1 q ρ = eqPts q ρ` from `kwS_one`
  (`16 ≤ |ρ| − 7`). ≈ 40 lines.
- **Template** `rsGSeg` from R3's `FRVIRTplChain` (and CF's `SG` layout so the closed forms apply):
  `phiG` 247; **F squaring chains** `sqChainF` for the 75 − 11 non-constant coordinates (claim 1's 7
  constants and claim 3's 4 zeros are constant forms): `64 × 127 = 8,128` gates; per stage and claim
  the product `Π_{l<25} (1 + a_l^{2^k} + ρ_l)` (`ofFK` lifts are linear; 24 `mulK` = 72 gates):
  `128 × 3 × 72 = 27,648`; `Σ_k c_k W_{j,k}` with `c_k ∈ F`: `128 × 3` `smulK` = 768; `κ^j`: 8.
  Input mux: `ρ`'s 50 cells × 3 kinds = 150 products, the claims' ≤ 2 kind-varying coordinates each
  ≈ 18. **≈ 36,970 gates = locals; + 75 forcing rows `one · f₁_cell = 0`** on the claims' K cells
  (the template reads `f₀` only; without the rows `KOk`'s "any register value" would take
  `rsWeightF`'s K-general branch). **K-general fallback** (`sqChainK`, no forcing rows): ≈ 45.1 k.
- **Padding.** The template is one instance at `n = 25` (L32); P30's 23 and N30's 24 coordinates
  enter with their missing coordinates muxed to `0` for both `r` and `ρ`: `1 + 0 + 0 = 1`, so the
  padded factors are the identity (`rsPlain_pad`, ≈ 30 lines; cf. R3 §4.1 L3, with no skeleton here).
- **Proof.** `ok_rsGSeg : … = rsPlain …` (R3's `ok_rsG` minus `kindG`, chains in F); `kRSS_ok : KOkD
  (implP impl₀ base 1 ι) ι kRSS` through `rsWeightF_seg`; `rtKD_okW`.
- **V.** Sparse: ≈ 37 k rows, ≈ 5–6 terms per row (R3: 6.3) ≈ 220 k terms at 0.24–0.33 µs ≈
  **55–75 ms VM once per check** (all segment slots and all kinds share it). CF: the chain groups
  (64 instances, stride 2^7) and the stage group (128 instances, stride 2^8: 222 gates padded to 256)
  are `Rep` groups with `Rep.tm_rep` closed forms ⇒ a few ms; padding adds ≈ 4 k rows/locals.
- **Init.** ≈ 0.25 s template + `instRow` (R3's rate: 472 k rows in 2.9 s), 0.1 s grouping, 0.05 s
  `repFitB`. Prover: 37 k locals per slot, gate evaluation in order (C1b §5.5).

### 4.5 The wrapper `rtKD` (new, generic; the one piece of mechanism)

`KOpD` = C1's `KOp` plus (i) one sub-template over **muxed inputs** (`Σ_ι sel_ι · form_ι`, zero past
the kind's width; the mux products are the template's first gates, so `kTpl`'s 3× copies are not
needed), (ii) **derived inputs**: locals (`shiftTarget`'s bits) or operand cells (`targetS`'s bits,
`rsWeight`'s `f₁`) with forcing rows, and (iii) the obligation `KOkD`: `KOk` under the derived facts
(`∀ regs, Der regs → …`). `rtKD_okW : KOkD … → RTOkW … B` is `rtK_okW`'s proof plus "the forcing rows
hold at `w'` and `InvK` gives the cell values, hence `Der`". One module ≈ 300 code lines, kernel
≈ 0.3 s. `rtC1d π := if π = 0 then rtN0c else rtLinkSegW repB |>.orElse rtEvZ |>.orElse (rtKD kTSS
…) |>.orElse (rtKD kSTS …) |>.orElse (rtKD kRSS …)`; `repOkW_rtC1d`.

## 5. Where the rows and cells go

**Rows of a segment region** (2^20; IMPC2's constants, `patch.py`): prototype `[0, 686,080)`; free
**band A `[688,128, 720,896)` = 32,768** (`21·2^15`; 2,048 rows of margin over the prototype, checked
at init as `ProtoFit` checks `InSlot`); arena rows from `arR2 = 720,896`: the binding/template index
space `arR2N = 180,560` of which p1 uses 135,997 (p0 114,320), arena₁ 96,944, bits 16,384, then
`repSegB`'s `2^10`, then the link region (32,768 reserved, ≈ 11.4 k used). **Request to the
integrator (FOLD2): cut `arR2N` to its used extent** (≈ 136,192 after 2^8 alignment; SEG-R0 measures
it on the dump as `arenafit` does): `arR1 857,088`, `arRb 954,112`, bits end 970,496, so **band B
`[970,496, 1,015,808)` = 45,312** (it absorbs the old `repSegB` range). Prototype 0's region is
unaffected (its rows end at 706,303 < `arR2`; both prototypes share the constants). Total ≈ 78 k.

**Cells of a segment region**: band 1 `[405,504, 441,152)` = 35,648 (above the bits, below the lowest
instance), band 2 `[277,402, 290,816)` = 13,414 (between the skeleton and arena₁): **≈ 49 k**. The
96 k of padding between the 3,033 instances and the 1.8 k at the top are unusable (the locals must be
contiguous, or strided for CF's rep groups). Moving prototype 1's arena cells down to 277,504 would
merge the bands (one band of ≈ 49.6 k) at the price of per-prototype `arA1`/`arBt` in
`FRNodeRows4ArenaPlace` (B2″/B4/IMPC2's `decide`s); the two-band map inside `repMapC` is local to
the replay track and is the recommendation.

| Per segment slot | rows | cells | note |
|---|---|---|---|
| `rsWeight` (F-point) | 37.0 k | 36.9 k | K-general 45.1 k / 45.1 k |
| `shiftTarget` | 3.1 k | 3.1 k | |
| `targetS` | 0.14 k | 0.13 k | |
| `evalM`, `evalL` zero rows; `linkWAll` (exists) | 14 | 0 | |
| **total** | **≈ 40.3 k** (K-general ≈ 48.4 k) | **≈ 40.1 k** (≈ 48.3 k) | CF padding ≈ +4 k each |
| **free** | 78 k in bands A, B (after the `arR2N` cut); 33.8 k without it | ≈ 49 k in two bands | |
| **margin** | 38 k | **≈ 9 k** (F-point); ≈ 1 k (K-general: reject) | |
| `N_M/1.05` | 49,000 allotted per segment region (`segRegion`); N8 stays 1.0185× | — | update the model's literal to the measured size |

**Definitions that move.** `repRow0 κ v` for `protoOf κ v = 1`: `k < 32,768 → v·2^20 + 688,128 + k`,
else `v·2^20 + 970,496 + (k − 32,768)`; `repMapC κ v`: frame cells as now, locals `repB + j ↦
oneCell + v·2^20 + (j < 35,648 ? 405,504 + j : 277,402 + j − 35,648)`; `repCellOk 1` allows those
cells; `repFitB 1`: rows ≤ 78,080, locals < 49,062; `RepFit` stays a plan-time Bool. Fit lemmas
(`rep_fit1`, `repReg`, `slot_rows_outside_rep`, `hfit4`): the two row bands are disjoint from the
prototype (`InSlot` plus the new init check `protoRows 1 < 688,128`), the arena rows (`arR2 ≤ …`,
constants), the bits' end and the link region; the two cell bands from arena₁, the bits, the skeleton
and the instances (`ProtoFit`'s `Nodup` plus the arena cell constants). The evaluation needs **no
band logic**: REPF groups a region's rows and cells by their 20 low bits, so `repV4` for segment
slots becomes `(Σ_{v ≥ 1} hiF t v · hiF u v) · rv₁` with `rv₁` the prototype-1 template value
evaluated once (REPF's `repV0_eq` pattern; today a segment slot's 8 rows are summed sparsely).
`evalMT4_eq`, `evalMX4_eq`, `slots_val`, `hfit4` keep their statements.

## 6. Totals

| | Δ | Basis |
|---|---|---|
| V per check (VM) | **+55–80 ms** sparse (once, shared); CF: + a few ms | §4.4; REPF's 0.24 µs/term |
| start-up | **+0.4 s** rows; **−1.6 to −1.9 s** `nodePlan` (if `implB` stops referencing it) | INIT §1, §5; R3 §4 |
| kernel | +3–5 s: `rtKD` 0.3, three templates' `Ok` ≈ 1 (R3: 0.85 for five modules), `rsWeightF_seg` 0.3, `FRNodeRows4Fit` bands 1–2 (route region facts through `p.1 / slotM4` as `rep_fit` does) | REPF §8.4, C1b §4.3 |
| rows / cells | ≈ 40 k / 40 k per segment slot; N2 +80 k, N4 +160 k, N8 +320 k rows (inside the 49,000 allowance) | §5 |
| `εR`, `\|π\|`, format, FS | unchanged | §3 |
| prover (E1) | locals from the plan-form dump (gate evaluation in order, F gates only after Karatsuba); zeros in the six dead cells; `f₁` cells and L bits already right | C1b §5.5 |
| residual after SEG-R | `impBP (rtC1d 1)` = the 7,426 siblings only (IMPC2b §5); `Gaps4` then needs the siblings and the closure generator (IMPC2b §1) | IMPC2b |

## 7. Plan

| Stage | Content | Done when | Kill line → exit |
|---|---|---|---|
| **SEG-R0** (measure; probes only) | On `logs/RSV2` and the FOLD2 dump: gate/local counts of `rsGSeg` (F-point and K-general), `tplSTS`, `tplTSS` at the three widths, built with `FRVIRTplChain`/CF's `SG`; the used extent of `[arR2, arR2 + arR2N)` per prototype; the two row bands and two cell bands as placed; V of the 3.x `evalMT nodePlan` per segment check (`vtime4 prof`); the `evalM`/`evalL` spec readers (grep, §4.1); confirm `r92569 = 1` and the Boolean L entries on the dump | a table rows/cells per op vs the bands; the `arR2N` request to FOLD2 with the number | locals > 49 k with the F-point form → merge the cell bands (per-prototype `arA1`) before R1; if still over, R3-style closed forms do not help (cells are physical): the exit is reducing arena₁ or the bit area (outside this track) |
| **SEG-R1** (Lean, mechanism and templates) | `rtKD`/`KOpD`/`rtKD_okW`; `implSeg` pin, `implC0`, `rtEvZ`; `rsWeightF_seg`, `rsPlain_pad`; `rsGSeg`, `tplSTS` (+ bit uniqueness lemma), `tplTSS` (+ range polynomial lemma); `kRSS_ok`, `kSTS_ok`, `kTSS_ok`; `rtC1d`, `rtC1d_ok`, `repOkW_rtC1d`; controls (+/− per op: perturbed operand, a non-Boolean L entry rejected, `f₁ ≠ 0` rejected, wrong kind select); KATs (honest locals satisfy every row, outputs = `targetSSegI`/`shiftTargetI`/`rsWeightF` at the three kinds) | build green, axioms clean, source rule 0; template sizes equal R0's | `rsWeightF_seg` does not close through 3.x's branches → state the template against `rsWeightS` and prove `implSeg`'s `rsWeight` meets it at `β = 1` (same lemma content, other route); a segment theorem reads `spec.evalM` → C2 proper (§3 (e)) |
| **SEG-R2** (fold, fit, plan, V) | `repRow0`/`repMapC`/`repCellOk`/`repFitB` two-band for π = 1; `arR2N` cut (with FOLD2); fit lemmas and `hfit4` re-proved (statements unchanged); `repV4` shared `rv₁` for segment slots; `repFit_of`/`repFold`/`gap4Imp_rtC1c` at `rtC1d`; `gaps4_of_runS` residual at π = 1 = siblings; plan-form re-dump; MxKat, `plan4t check` N2/N4/N8; V(N2/N4/N8) and `plan4t init` A/B; `FRNodeRows4Model.segRegion` literal updated | `HARNESS`-side: V(N4) Δ ≤ 100 ms VM, init Δ ≤ +0.5 s before the `nodePlan` cut, kernel Δ ≤ 5 s; `impBP (rtC1d 1)` has no replay op | V Δ > 150 ms → CF's closed form for `rsGSeg` first (it is on CF's path anyway); init Δ > 1 s → the template built from the final compile state, `rowsTR`, no second walk (REPF §3) |
| **SEG-R3** (prover, closed form) | E1: locals for the segment slots from the dump, zeros in the dead cells, `node-kat`; CF: `Rep` closed forms for `rsGSeg`'s chain and stage groups | end-to-end `check.sh` accepts; V(N4) with closed forms measured | — |

R0 is one agent-stage with scripts; R1 is independent of FOLD2 (its modules import nothing of the
fold) and can run in parallel with CF; R2 waits for FOLD2 (the `arR2N` constant and IMPC2's rows) and
R1; R3 after R2. Reviews per the user's ruling: a cheap Opus pass on each stage.

## 8. Open questions

1. **`arR2N`'s slack**: is the unused 44.5 k at the top of `[arR2, arR2 + arR2N)` or interleaved with
   the stride structure (`LvIn`)? R0 answers; if interleaved, band B shrinks and band A + the old
   `2^10` (33.8 k) do not hold ≈ 40 k rows, so the cut must move the ask template rows down as well.
2. **The 3.x `evalM` per segment check**: its V cost is unmeasured; if it is tens of ms the pin is
   worth doing first and alone.
3. **CF's padding on the segment template**: CF chooses `p` per group; the cell margin (≈ 9 k) bounds
   the padding at ≈ 20 %. If CF needs more, the segment template keeps sparse evaluation (≈ 60–80 ms).
4. **The forcing rows `f₁ = 0`** are redundant with the `mulKF` prototype rows; a later golf can drop
   them if `KOkD` is given the compile's own rows instead (not worth it now).
