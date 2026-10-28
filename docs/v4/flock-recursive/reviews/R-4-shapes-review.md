# R-4 (revision 4.1's shapes, S-0′'s `FR.Rev4` layer): adversarial review

Reviewed: `stages/S-0p-RESULT.md`; `FRShape4` (199 code lines), `FRSegment` (81), `FRAgg` (238),
`FRVerifier4` (135), `FRNodeLayout4` (45), `FRVIR4` (111) at commit `47c5c6c`.

HEAD moved during the review:
- **`de5aecb` (S-F4)** added `SegSoundOn`/`SegKSOn`/`segSoundOn_of_KS`/`VA_extract_on` to `FRAgg`
  and `lastOps` to `FRVIR4` (its message: "`SegSound` unprovable for FS verifiers").
- **`43b34e1` (S-D3)** declined lever 5 (`ell0 = 5`).

The other four files are unchanged at `43b34e1`. The additions are not reviewed in full; each
finding says whether it still applies at `43b34e1`.

Spec: BLUEPRINT status header, §0, §0.1 B-11 … B-17, §10 changes 25–26. Contract: `.contract` at
`6d05d00` (`Relation`, `Security`, `Oracle`, `Certificate`, `Tree`), plus `FRKState.FinalLaw`, the
entry's route to `KS`.

## Evidence

| Check | Result |
|---|---|
| Probe tree `logs/R-4/build` (a `47c5c6c` snapshot of `lean/`, `.lake` copied from `fr-build-S0p`, against `logs/org20`) | `lake build R4Probe` is green (`logs/R-4/probe-build.log`); `R4Probe` takes 18 s. All under `systemd-run … MemoryMax=16G`, `timeout 1500`. Sources: `logs/R-4/sources.sha256` |
| `not_segSound_lucky` (kernel) | **`¬ SegSound VsegLucky vk`**, where `VsegLucky` asks one query and accepts iff the answer is the zero digest. Its false-acceptance probability under a random oracle is `2^-256` per proof (R-4-M1) |
| `segSoundLog_lucky`, `VA_sound_log`, `VA_extract_log`, `VA_rel_log`, `V4_agg_extract_log` (kernel) | the minimal fix for M1 and M2: segment soundness on a good **log** under `runLog`, with `1 ≤ n`. `V_A` then extracts `Rel`'s leaf clause in `FinalLaw`'s shape. The proof is S-0′'s, with the split removed |
| `aggChain_k3` (kernel) | `aggChainLen 3 = 69,504`, and the last block holds 62 bytes: **`k = 3` is unaligned too** (R-4-m2) |
| `lSlots_fit`, `lSlots_N8_full` (kernel) | `vslots · 2^14 ≤ N_L` for every node kind; for `N8` it is an equality (R-4-m4) |
| `#eval` at `ell0 = 5` (`seqOfR 5` over the six kinds; `logs/R-4/probe-eval.log`) | 9,778 items (against 8,905), `4 × 9,778 = 39,112 > qV4`; `piSizeOf` 830,160 (with 3.x's 64-row columns, see R-4-m3) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` only, for every probe theorem |
| Reading | `VAwith`, `aggChecks`, `VA_extract`: every check is traced to its use. `kindOf4`/`V4with`: every branch. `genPhase4`'s dummy handling (`realRounds` → `roundOpsF`/`roundOpsK`'s `assertZero`). The layout numbers, recomputed by hand |

## Answers to the seven questions

1. **`V_A`.**
   - **What it binds.** It binds the start (`aggWit` reads segment 1's `hdr.pub`), the end
     (`e_k = e`), the length (`Σ nᵢ = n`), the order (`chainOk` on raw bytes; `pubStart` is
     positional), the statement (`c = leafStmt e n`) and the trace (`seqAll`, used up exactly).
     Every check except `1 ≤ nᵢ` is used by `VA_extract`.
   - **Reordering, dropping, duplicating and splicing** either break `chainOk`/`Σ`/`e_k` or yield a
     valid continuation of the same chain. Given segment soundness, no edit of the segment list
     defeats extraction.
   - **`VA_extract`'s conclusion** is exactly `Rel`'s leaf clause (`VA_rel_log` derives
     `Rel acc c (.leaf s n)` for any `acc`).
   - **`SegSound`** does not smuggle in the aggregate result. But it is too strong to ever hold for
     the real programs, in two independent ways (R-4-M1, R-4-M2).
2. **`segs_compose` and `seg_sound`.**
   - Both are correct. `seg_sound` is `leaf_sound` at `n`. `segs_compose` is `chainEnd_add` by
     induction.
   - In this layer, only `segs_compose` is on `V_A`'s path. `seg_sound` is reached only through the
     assumed `SegSound`: the link from a segment proof's bytes to `SegHolds` is S-C/S-G's.
   - **Controls.**
     - `ctrlA_bad_sum` and `ctrlA_bad_start` are rejected, and the same proofs with the right `n`
       and start are accepted (`ctrlA_pos`). So they discriminate.
     - Missing: negatives for `e_k ≠ e` and for `k ∉ [1, 4]` (R-4-m4).
     - `segs_compose_ctrl` is only the definition unfolded.
3. **Dispatch.**
   - **A bare segment** is rejected by `kindOf4` (`.bad`, no query), at top level and as a node
     child (`acc` runs `V4with`). This is a design choice: a bare segment would be extractable
     anyway.
   - **Kind bytes.** `bytes_distinct` covers the nine first bytes. `kindOf4` tests `'A'` first, and
     `kindOf4_encode` keeps `W` complete.
   - **`W` proofs** work as in 3.x (`V4_W_sound`, `V4_encode`, `ctrl4_W_leaf`).
   - **`acc_eq4`** is an honest equality: it mirrors `Submission.acc`, including PR #20's word
     conjunct.
   - **`complete4`** is honest and non-vacuous: it is the contract's `CompleteWithError` for
     `P := encode`, as B-10 intends. But it holds for every `Vseg`/`Vnode`, including programs that
     reject everything, so it is no evidence for the `A`/node path. That path has only `VA_complete`
     (conditional on accepting segment runs) and `ctrlA_pos` (with `VsegTrue`). The RESULT should
     not cite `complete4` for the new shapes.
4. **`seq4`.**
   - **The 3.x pins.** `phasesOf_seq3` (by `decide`), `itemsOf_seq3` and `piSizeOf_seq3` are real
     fidelity checks: the parametric generator at `seq3` reproduces 3.x. Their docstrings, however,
     claim something false under 4.1 (R-4-m6).
   - **`qV4 = 36,000`.** It is within the certificate's `qV ≤ 2^16` and far below `logCap = 2^96`.
     The margin is 1.07 % (`4 × 8,905 = 35,620`), and it breaks at `ell0 = 5` (R-4-m3).
   - **The 14 extra items.** Their payloads are asserted zero for every kind that does not use them.
     A dummy round's 48/96-byte message gets `assertZero` when `j ≥ realRounds`. A segment's
     `Lrend`/`Eend` are asserted zero. The extra squeezes carry no payload. A segment's 32-byte
     `E4end` absorb stays free, as in 3.x; that is harmless.
5. **Layouts.**
   - **The numbers.** `hUsed_eq`, `regions_fit`, `mSlots_fit` and `coords_eq` are right; I
     re-derived all of them.
   - **`τ`/`σ`.** `τ = log N_M` = 22/23/23 equals E2's rounds. `σ = m − 7` = 24/25/25 equals E4's.
     So I-3 is consistent, and the blueprint's "`σ` 23" is the stale figure.
   - **`N_L`.** The `2^14` stride is 3.x's per-slot stride (3.x uses 8,519 cells of it).
   - **What is missing.** No lemma shows that the L region holds the slots (R-4-m4).
   - **`N8` is full.** Its L and M are exactly full. The 7,936 blocks between L's end and M's base
     (1.04×) are all that is left for I-5's padding rows, O-1's `c_A` block and the `k`-mux.
6. **S-0′'s open points.**
   - **I-5 is a soundness obligation**, not only a circuit task, and it misses `k = 3` (R-4-m2).
   - **I-6 is harmless for `KS`.** `VAwith` and `aggWit` never read bytes 2–7. But it makes `π_A`
     malleable 2^48-fold, so the node extractor's reassembly must fix those bytes (R-4-m5).
   - **O-1 is consistent.** Under `V_A`'s own checks `e = e_k`, `n = Σ nᵢ`, the circuit's
     "`(e, n)` = a preimage of `c` with `e = e_k`, `n = Σ nᵢ`" accepts exactly when `V_A` does on
     `hdrA := 'A' ‖ k ‖ 0^6 ‖ enc64 n ‖ e`, and the extractor writes that header. In-circuit,
     `Σ nᵢ` over `GF(2^128)` needs a binary adder: field addition is XOR.
7. **Against the contract.**
   - **No conflict** with `Relation` (the leaf clause matches), `Tree` (unused) or `Certificate`
     (`qV`, the word conjunct, `|π_A| ≤ 3.05 MiB` inside `Computes`' 128 MiB domain).
   - **The contract-facing gaps:**
     - `V_A`'s soundness is stated for `runSeq`, while `KS`/`FinalLaw` read the verifier through
       `runLog` (R-4-M1);
     - `KS`'s first conjunct (`V` asks at most `qV` queries on every input) has no lemma for
       `V4with` (R-4-m4).

## What is right

- **`V_A`'s check list is exactly what the leaf clause needs.** The proof of `VA_extract` uses each
  check once:
  - `c = leafStmt e n` for the statement;
  - `1 ≤ k` for a first segment;
  - `k ≤ 4` and `nᵢ ≤ cap κᵢ ≤ 2^18` for `n ≤ chainCap`;
  - `Σ nᵢ = n` and `e_k = e` for the endpoints;
  - `chainOk` for `segs_compose`.

  All checks run before any query.
- **`aggWit` is a total function of `π` alone**: segment 1's `hdr.pub` and `hdrA`'s `n`. This is the
  simplest extractor branch possible, and `Computes`-friendly.
- **`seqAll` with `runSeq_bind_some`/`runSeq_bind_of`** gives the split and its converse
  (`VA_complete`). `VA_complete` is the lemma S-G's `node_sound` needs for an `A` child: from
  piecewise runs plus the checks to `acc` on `tr_A`.
- **I-2 is sound and simpler than B-12's gated row.** Every segment's start sits in `hdr.pub`. The
  seed `"FRSEED0" ‖ vk ‖ cᵢ ‖ hdr` binds it, the shift boundary pins block 0 to it, and `V_A` checks
  `s_{i+1} = e_i` on raw bytes. I concur with I-2.
- **The dispatch is tight.** `'A'` is tested first. A node byte with the wrong size and a bare
  segment are rejected with no query. `W` keeps its 3.x guarantees.
- **The generator.** It is a faithful parametrisation. The dummy rounds are zero-asserted through
  `realRounds`, and the ladder fits are proved (`seg_ladder_fits`, `node_ladder_fits`).
  `fieldOffs` documents that `seq4`'s offsets move.

## Majors

### R-4-M1. `SegSound` quantifies over every trace: no Fiat–Shamir segment verifier meets it, and it is not the form `KS` consumes (owner: S-0′, with S-G12′)

**Location.** `FRAgg.SegSound` (l. 164), `VA_extract` (l. 204), `FRVerifier4.V4_agg_extract`
(l. 136); RESULT §3 ("`VA_extract` … This is `Rel`'s leaf clause") and §7 item 2.

**What it says.** `SegSound Vseg vk` is
`∀ π v t, segView π = some v → v.n ≤ cap → (Vseg …).runSeq t = some true → chainEnd v.start v.n = v.h`.

This is **perfect soundness against an adversary who chooses every oracle answer**. Under
`runSeq`, the trace `t` answers each query with whatever it lists. It need not even be a
function: the same query may get two answers.

**The attack.** For the real segment program (`runIR … (genSeg κ fin)`), a trace that picks the
squeeze answers picks the zerocheck point, the sumcheck challenges and the fold challenges, and it
answers every `askNode` with the digest the Merkle check wants. A false chain claim is then
accepted:
- choose the round messages first, then the challenges at which they agree;
- open columns that the "hash" answers certify.

So `SegSound` is false for the real `Vseg`, and `VA_extract`/`V4_agg_extract`, though true, can
never be applied to the submission.

**Kernel check.** `not_segSound_lucky` (`logs/R-4/build/src/R4Probe.lean`):
- `VsegLucky` asks one query and accepts iff the answer is the zero digest. Under a random oracle
  it accepts a given proof with probability `2^-256`.
- It fails `SegSound`: the 96-byte `L31` segment claiming `0 → 0` in one step, with the trace
  `[(π, 0)]`, contradicts the KAT `chainEnd 0 1 ≠ 0`.
- It meets the log form below on the logs with no zero answer (`segSoundLog_lucky`), an event of
  probability at most `#queries · 2^-256`.

**Why the form matters.** The entry's route to `KS` is `FinalLaw` (`FRKState`, l. 33):
`∀ L c π, L.length ≤ logCap → μ L < 1 → (S.V vk c π).runLog L = some true → ∃ w, E c π L = some w ∧ Rel …`.
- The verifier is read by **lookup in one log** (`runLog`), never against a trace.
- Soundness holds only **on good logs** (`μ L < 1`).

Under `runLog`, all of `V_A`'s segment programs read the same `L`, so no split is needed, and one
potential below `1` covers every segment at once. There is no factor `k` in the error, since
`FinalLaw` is `∀ c π` already.

**Status at `43b34e1`.** `de5aecb` reached the same diagnosis and committed `SegSoundOn`, which
adds a `Good` predicate. Its form is still not `FinalLaw`'s:
- it keeps `runSeq`;
- `VA_extract_on`'s `hG` requires `Good` of every piece of every split of `tr`, which is every
  infix of `tr`. That holds for a per-entry predicate, but a potential on logs (`μ L < 1`) does not
  provide it.

`FinalLaw` gives one log `L` and reads `V` with `runLog`, so `SegSoundOn` would need a further
bridge from `runLog` on `L` to `runSeq` on good pieces. The `runLog` form below needs none.

**Minimal fix** (kernel-checked in the probe; about 60 lines beyond what S-0′ already has):

```lean
def SegSoundLog (Vseg : SegProgs) (vk : Digest) (Good : Log → Prop) : Prop :=
  ∀ L π v, Good L → segView π = some v → 1 ≤ v.n → v.n ≤ v.kind.cap →
    (Vseg v.kind vk (segC v) π).runLog L = some true → chainEnd v.start v.n = v.h

theorem VA_extract_log (hS : SegSoundLog Vseg vk Good) (hG : Good L)
    (h : (VAwith segSize Vseg vk c π).runLog L = some true) :
    ∃ s n, aggWit segSize π = some (s, n) ∧ n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n
```

The probe also proves the supporting lemmas:
- `runLog_bind` and `runLog_seqAll`;
- `VA_sound_log`;
- the `V4with`-level `V4_agg_extract_log`.

S-G instantiates `Good L := L.length ≤ logCap ∧ μ L < 1`. Keep `VA_sound`/`VA_complete` (`runSeq`)
for `node_sound` and `acc`. Replace `SegSound`, `VA_extract` and `V4_agg_extract` (or demote them
to toy-only lemmas). Change RESULT §3/§7 accordingly.

### R-4-M2. `SegSound` covers `n = 0`, where the planned segment program proves a full-length chain (owner: S-0′; also the worktree's `SegSoundOn`/`SegKSOn`)

**Location.** `FRAgg.SegSound`: its only range hypothesis is `v.n ≤ v.kind.cap`.

**The attack.**
- The variable last block reads `L = n − 1` from `stmt` bytes 33–40 as 18 bits: RESULT §5,
  "`bnd[4 …]` must be the bits of `nᵢ − 1`"; S-F4's `lastOps` borrow chain; `FRSegTarget4`, "zero
  above the kind's `m − 14`".
- At `n = 0` the borrow chain gives all ones, so `L = cap − 1`, the same as at `n = cap`.
- So the honest prover, run on a full segment `s → chainEnd s cap` with `stmt`'s `n` field set to
  `0` (and `cᵢ = leafStmt h 0`), produces a proof the program accepts.
- `SegSound` then demands `chainEnd s 0 = s = h`, which is false. No luck is needed.

**Why `V_A` is still sound, and the cost.**
- `V_A` already checks `1 ≤ nᵢ` before running any segment. But `VA_extract` never uses that check
  (only `(hr _ hv).2` is used), so the assumption was silently made stronger than `V_A` needs.
- **Still open at `43b34e1`.** `SegSoundOn` and `SegKSOn` (committed in `de5aecb`) keep `n ≤ cap`
  as their only range hypothesis. At `n = 0`, `SegKSOn` asks for a `SegHolds` table, which cannot
  exist because `InRange` needs `1 ≤ n`. So it requires the program to reject every `n = 0` proof,
  while `lastOps` (in the same commit) accepts them as full-length chains.
- Left as is, discharging the assumption needs an extra `n ≥ 1` range row in every segment
  circuit, or fails.

**Fix.** Add `1 ≤ v.n` to the hypotheses: `SegSoundLog` above does. `V_A`'s check then becomes
load-bearing (the probe's `VA_extract_log` uses `(hr _ hv).1`). Optionally add
`π.size = piSizeOf seq4`, which `V_A` also guarantees, so that the real program need not check its
own size.

## Minors

### R-4-m1. `pubStart` is a dead field, and the docstrings describe a pin that does not exist

`SegHolds` never reads `st.pubStart`, yet its docstring says "the gated pin when `pubStart`".
`Chained` is never used. The only consumer of the flag is `compose_views`' bookkeeping. Under I-2,
the start is `hdr.pub` for every segment. B-12 still describes the gated row and segment 1's
"secret start".

**Fix.** Drop `pubStart` from `SegStmt` (and `Chained`, `SegView.stmt`'s flag), or document it as
positional only. The orchestrator then rules on I-2 and rewrites B-12.

### R-4-m2. I-5 omits `k = 3`, and the padding is a soundness obligation, not only a circuit task

`1 + k · 1,482,751 ≡ 1 − k (mod 64)`, so `k = 2, 3, 4` are all unaligned: 63, 62 and 61 bytes in
the last block (`aggChain_k3`). `k = 3` is `N4`'s main case (B-13: `N4` for `k = 3, 4`).

**Why it is a soundness obligation.** The node must compute `traceDigest tr_A` exactly:
- the zero padding of the last block;
- the byte counter;
- the final flag on a block whose position depends on `k`.

`KS` is `∀ vk`, so the adversary may hold the signing key (`Certificate`'s "why every key"). If the
padding cells or the counter are free, it signs the digest of a stream other than
`0x54 ‖ traceBytes tr_A`. The node accepts, but the extracted child fails
`SigOk vk (traceDigest tr_A)`, so `acc` is false and extraction fails.

Likewise, `N2` must refuse an `A` child with `k > 2`: its H holds only `aggChainLen 2` blocks.

**Fix.** List these three items (`k`-gated padding zeros, counter and final block; the `k ≤ 2` bound
for `N2`) in S-E12′'s row list and S-G12′'s truths. Correct I-5 and `FRNodeLayout4`'s docstring
to `k ∈ {2, 3, 4}`.

### R-4-m3. `ell0` is not parametric, and `qV4` breaks at `ell0 = 5`

I-7 claims level-0 rows are a parameter (`Seq.ell0`, `ladderOfR`). Three places hard-code `6`:
- `colBytes` (`FRTranscriptDefs`, l. 110: `lvlStar` rows) feeds `itemsOf`/`piSizeOf`/
  `streamBytesOf`;
- `finalOps4` asserts zero beyond `2^(m − 25)`, while the kind's final message is
  `2^(m − 19 − ell0)`. At `ell0 = 5` it would zero-assert 128 real `K` elements, which breaks
  completeness;
- `Dims.seq`/`seqOf` use `seqR 6`.

**Measured at `ell0 = 5`** under S-0′'s own `ladderOfR` (`probe-eval.log`):
- every level's `log n` rises by 1 at fixed caps, so each position gets one more sibling;
- 9,778 items, and `4 × 9,778 = 39,112 > qV4 = 36,000`. Honest 4-segment aggregates would then
  fail `accWith4`'s `tr.length ≤ qV4`.

**The blueprint's lever 5 figures disagree.** Changes 26 lever 5 is in design C′, yet it says
"siblings +9 KB" and "a sub-slot's trace … ≈ 19,400 blocks". With the ladder rule there are +871
siblings (≈ 27.9 KB), and with 32-row columns the stream is ≈ 1,436,080 B ≈ 22,439 blocks.

**Status at `43b34e1`.** S-D3 found the same `qV` figure (39,112) independently and declined lever
5, so the `qV4` breakage and the lever-5 figures are moot. What remains is I-7's claim: `Seq.ell0`
and `ladderOfR`'s parameter suggest a parametricity that `colBytes`, `finalOps4` and `seqOf` do not
have.

**Fix.** Either drop the parameter (`ell0 = 6` is the ruling), or thread it through `colBytes`,
`finalOps4` (`2^(m − 19 − S.ell0)`) and `seqOf`, so that a later lever cannot silently mis-size the
format.

### R-4-m4. Missing statements and controls

- **`KS`'s query bound.** `KS`'s first conjunct has no lemma bounding `((V4with …).queries H).length`
  by `qV4` from per-program bounds:
  - `W`: 0;
  - `A`: at most 4 × `Vseg`'s, since `k ≤ 4` is checked before any query;
  - node: `Vnode`'s.

  `traces_le_qV` is about items, not programs.
- **The L region.** No lemma shows that it holds the verifier slots: `lSlots_fit` (probe),
  `vslots · 2^14 ≤ N_L`. `N8` is exactly full (`lSlots_N8_full`), as is its M (`mSlots_fit` with
  equality).
- **`V_A`'s negative controls** cover the sum and the link only. Add `e_k ≠ e` and `k ∈ {0, 5}`, and a
  segment whose `n` is out of its own kind's range but within `L32`'s, to show that `cap` is
  per-kind.

### R-4-m5. `hdrA` bytes 2–7 are free (I-6): harmless for `KS`, but `π_A` is not canonical

Neither `VAwith` nor `aggWit` reads bytes 2–7. So `KS` is unaffected.

But 2^48 byte strings `π_A` are accepted for one `(tr_A, c)`. The node's extractor reassembles
`π_A` from the trace and must choose these bytes. `n` and `e` are also not in `tr_A` (O-1), but they
are determined by the segments.

**Fix.** Add `bytesAt π 2 6 = 0` to `aggChecks`. Honest proofs and the controls are unaffected.

### R-4-m6. Docstrings that state something false under 4.1, and dead code

- **`itemsOf_seq3`**: "The segment sequence is 3.x's `items`". Under 4.1 segments use `seq4`.
- **`piSizeOf_seq3`**: "A segment proof has 3.x's `piSize`". It is 798,192 B, not 797,904.
- **`fieldOffs`**: "The segment format's field offsets are 3.x's". They are `seq4`'s.
- **`FRShape4`'s header**: "Revision 4.0's shapes … the two item sequences".
- **`ladder_sq_sib`**: "`m ∈ {31, 32, 33}` (… 33: `N8`)". The theorem states 31 and 30.
- **`FRAgg`'s header** cites `ctrlA_bad_stmt`, which does not exist (`VA_reject_stmt` does).
- **`segs_compose_ctrl`'s docstring** names `Chained'`.
- **Dead code**: `Chained` and `NodeKind.aggSegs` are never used. The second also shares a name
  with `FR.Rev4.aggSegs`.

### R-4-m7. Blueprint text that contradicts the 4.1 shapes as built (owner: orchestrator)

- The status header still says "revision 4.0".
- §0's summary: `N8` at `m = 33`; kinds `L31`/`L32` only; "`≤ 4 × 8,891`".
- B-11: "`L31` for a remainder", "`N4`/`N8`".
- B-12: the gated `pubStart` row (against I-2).
- B-13: "slot 1 muxed over `{N4, N8, A}`", "sub-slots `{L31, L32}`". The RESULT has `{N2, N4, N8}`
  and `{L30, L31, L32}`.
- §0: "`τ`/`σ` 23 coordinates" (`σ` is 25).

## Verdict

**Not yet a base for S-G12′ and S-H2n.** The layer's logic is sound:
- `V_A`'s checks are exactly the leaf clause's. Every one but `1 ≤ nᵢ` is used, and M2's fix makes
  that one load-bearing too.
- The dispatch is tight.
- `seq4` and the layouts are consistent with the contract's caps (at `ell0 = 6`).

Its soundness interface, `SegSound`, cannot be discharged:
- it demands perfect soundness against chosen oracle answers under `runSeq` (M1, kernel
  counterexample);
- it covers `n = 0`, which the planned program maps to a full-length chain (M2).

Both are fixed together by the `runLog` form with `1 ≤ n` (`SegSoundLog` →
`VA_extract_log` → `V4_agg_extract_log`), already kernel-checked in `logs/R-4/build/src/R4Probe.lean`
on top of S-0′'s own lemmas.

At `43b34e1`, `SegSoundOn`/`VA_extract_on` fix M1's "every trace" but not its form (`runSeq`,
`Good` on every piece), and M2 is untouched.

**Once M1 and M2 are applied, the layer is fit to build on.** Answer the minors in the fix pass.
m2 changes what S-E12′ and S-G12′ must deliver (the `k`-gated padding, counter and final block;
`k ≤ 2` in `N2`).
