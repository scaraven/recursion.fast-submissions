# A3′ RESULT: blocked. The batched cap check (β) is unsound as built; the certificate cannot be restated

Track A3′, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `f853d37`.
Build tree `logs/fr-build-A3`, logs `logs/A3p/`. Journal: `stages/A3p-JOURNAL.md`. No sub-agents,
nothing committed, **no source file changed**.

## 0. Summary

- **Stopped at item 1.** PACK §3.3's soundness argument, and the A3′ restatement in §9.1, need the
  path digests `cur_r` to be fixed before ζ: "a polynomial of degree ≤ 870 in ζ whose
  coefficients are fixed by items ≤ Q.4, before ζ".
- **They are not fixed.** The Fiat–Shamir chain absorbs no column, no sibling and no path digest:
  - `fsItems4` is "the item sequence without the column and node queries";
  - Q.i has no Fiat–Shamir item (`fsStarts4`: Q.i and P3.i both start at 370, 397, 421, 443, 463).

  So ζ and z are functions of the chain alone, and the prover picks π's columns and siblings after
  both are known.
- **The consequence is a practical forgery, not a proof gap.** `F` has characteristic 2, and (I)
  is GF(2)-linear in the digest bits. Bellare–Micciancio's linear-algebra attack opens arbitrary
  (uncommitted) columns that pass (I) and (II). It costs about 20 k compressions and one
  512 × 871 GF(2) elimination (§2).
  - `ks_rev4H`/`certificate_rev4H` at A2′'s V are therefore **false** at any small ε, with
    `logCap = 2^96` to spare.
  - No restatement can make them build. In particular `pathDig (L, es)` does not exist: V's
    `cur_r` is a function of π.
- **ε**, as asked: `D_ζ ≤ 870/2^256` and `D_z ≤ 1,407/2^256` both fit inside εR's slack (§3). That
  is moot until the construction binds `cur_r`.
- **Fix: bind the path digests in the chain before the batching challenge** (§4). The cheapest
  sound variant I see overflows N8's H by 1,280 blocks. The orchestrator must rule.

## 1. What V does (A2′'s code, read)

- `FRVIR4.posOps4`:
  - `piField 0 (co + p·colBytes i)`: the column, from π;
  - `merkleOps4 … (so + p·sib·32)`: the siblings, from π;
  - `shrN`: the cap index.

  There is no compare. `cur_r = curOfY sL y` is the path's root.
- `FRVIRFinals4.capChkOps`:
  - `ζ = chK` of `(lvOuts fi 4 4)[1] − 1`: P3.4's first answer;
  - `z = chK` of CapChkZ's answer;
  - `aL += ζ^r·lo(cur_r)`, `aH += ζ^r·hi(cur_r)` (`splitDigest`, `mulKF`, `addK`);
  - `aZ`, and the entries' sums with `A` (π field 18);
  - three `assertEq`.

## 2. The attack (journal §4 has the details)

- **Linearity.** Fix ζ. Then `φ_r(d) := (ζ^r·lo d, ζ^r·hi d) ∈ K² ≅ GF(2)^512` is GF(2)-linear in
  `d`'s 256 bits (`CharP F 2`, `CharP K 2`).
- **The identities.** Let `T := Σ_k A_k·(lo cap_k, hi cap_k)`, with `A` the honest vector for ζ and
  the `k_r`. Since `A` is honest, (II) holds exactly, and (I) reads `Σ_r φ_r(d_r) = T`.
- **Two openings per read.** For each read, take two openings whose fold is the value the prover
  needs (e.g. one top sibling changed: one compression). Call their roots `d_r⁰` and `d_r¹`.
- **The linear system.** Solve `Σ_r b_r·φ_r(d_r¹ − d_r⁰) = T − Σ_r φ_r(d_r⁰)` over GF(2). There
  are 871 unknowns and 512 equations, and the system has full rank except with probability
  `≤ 2^{−358}`. Open read `r` with `d_r^{b_r}`.
- **Why this forges.** The openings are free, so a cheating prover answers every query with a
  column of the encoding it needs (Ligerito without binding). The PIOP's committed word is then
  never checked, and a false statement is accepted.
- **Any per-read additive batching fails the same way.** A logUp form fails too, and it is worse
  in characteristic 2: a repeated fake digest cancels mod 2.

## 3. ε (the brief's question)

| Row | Where | Bound | Budget | Fits |
|---|---|---|---|---|
| `D_z` | phase 53, single squeeze (`hsingle`) | count 1,407 | `N = 239·2^128` (`N_le`) | yes |
| `D_ζ` | P3.4's 5-squeeze phase (`hround`; `finP3 4 = finP2 4` today, no κ_c row) | `870/2^256` | `deltaR = epsD − 2^{−142}`, ≈ `15/2^124` | yes |

With these rows `εR = 15/2^124` and `claim.json` would stand. But `D_ζ` cannot be stated (§0).

## 4. Fixes, for the orchestrator (numbers from A2′'s §6 constants)

1. **(β′) Bind, then batch.** The phases after `Pf`:

   ```
   absorb D (field 19: the 871 path digests, 27,872 B); squeeze ζ;
   absorb A (45,088 B); squeeze z
   ```

   - **V.** Per position, a **static** `piDigest (fieldOff D + 32r)` and `assertEq cur`. The index
     is static, so there is no mux: this is what B2 needed. (I)/(II) then run on `D`, and PACK's
     SZ argument holds, because `D` is in the chain before ζ.
   - **The dooms.** `D_ζ`/`D_z` become prefix-determined, with `pathDig := D_r` from the chain.
     §9.1's statements then work, with `D_ζ` at the new ζ squeeze.
   - **Stream.** `80 + 27,872 + 80 = 28,032 = 64·438`, still whole blocks. A segment is then
     `1,556,032 = 64·24,313` bytes.
   - **N8.**
     - Stride 24,315, and `aggL 4 = 97,258`.
     - `hUsed = 2·97,258 + 2,196 = 196,712`, `hEnd = 196,720`, and `lBase = 196,864`.
     - The bound is 195,584, so **N8 overflows by 1,280 blocks**. Today's spare is 2,304
       blocks, and 8 slots × 438 = 3,504.
   - **Other sizes.** `|π| = 871,152`. Items 8,909, so `qV = 35,639 ≤ 36,000`.
2. **N8 levers to make (β′) fit.** This is the orchestrator's call: 7 segment slots; or a
   smaller `A`; or deeper caps at some level, which PACK §3.2 priced.
3. **Revert to the pre-A2′ V.** That V does a per-position dynamic `piDigestAt` and `assertEq`,
   and it is sound. The chain at HEAD `4d5700c` is certified. It keeps the R1CS mux cost that B2
   was meant to remove.

PACK §3.2's table and the PACK review (PK-*) both miss this. The phrase "fixed by items ≤ Q.4"
treats V's query order in the stream as if it were the Fiat–Shamir chain. Column and node queries
are stream items, not chain items.

## 5. State left

- **Source.** No module edited. The worktree is A2′'s HEAD, red in `FRSoundness4TailD` and
  `FRSoundness4R4Run`.
- **Build tree** `logs/fr-build-A3`:
  - a copy of `fr-build-orch`, with `fr-build-A2`'s oleans;
  - `snap.sh` pinned to the main worktree's `logs/pkgs` and `logs/org20`, the paths the oleans were
    built against;
  - `MINE="FRSoundness4TailD FRSoundness4R4Run"`.

  The baseline `./b.sh FR` reproduces A2′'s two red modules (`logs/A3p/build-0-baseline.log`,
  2,575 jobs).
- **Not done.** Items 1–5 (restatements, `482 → 484`, the re-run, controls, checks). Each depends
  on the ruling in §4. Under (β′), §9.1's plan applies almost unchanged, with `pathDig := D_r`
  and the position checks restated to `cur = D_r`.

## 6. Open questions

1. Which fix: (β′) with an N8 lever, the revert, or another binding?
2. Under (β′), should ζ stay P3.4's? It cannot: ζ must come after `D`. So (β′) has two new
   squeezes, and PK Q1's "a fresh ζ buys nothing" is withdrawn.
3. Should A2′'s V go back to `4d5700c`'s V until the ruling, so that `v4/rev44` does not carry an
   unsound verifier?
