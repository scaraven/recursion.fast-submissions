# PACK-4.4 §11 (β′): adversarial review (b2)

Reviewed 2026-10-29: `docs/v4/flock-recursive/design/PACK-4.4.md` §11 at HEAD `6bc442c` of the
main worktree, against the code in `recursion.fast-submissions-rev44` at `ccdde20` (A2′'s V, read,
not built), A3′'s result (`stages/A3p-RESULT.md`), the first review (`reviews/PACK-4.4-review.md`)
and the harness rules (`.contract/harness/PROVER.md`). No sub-agents, no commits, no Lean build:
every claim below is read off a definition (file and line named) or recomputed in
`/tmp/claude-1000/-home-devops-Verified-zkEVM-recursion-fast-submissions/bf7d5184-7235-4e88-9ffb-5830921b0802/scratchpad/recompute.py`.

Findings: `PB-M<i>` major (must fix before the brief is issued), `PB-m<i>` minor. Verdict in §5.

## 0. Summary

- **(β′) is sound in the model the certificate proves, and I could not break it** (§2). Every
  summand of (I) and (II) is a function of the chain prefix at the squeeze it is multiplied by:
  `D` (absorbed at FS entry 482, before ζ at 483), `cap` (the `cap0`/`C.i` absorbs), `k_r` (P2.i's
  answers, the kind from the seed), `A` (absorbed at 484, before z at 485). The only π-read values
  that are not chain values, the columns and siblings, are bound to `D_r` by the static assert at
  every one of the 871 positions of every kind, and a second opening to the same `D_r` is a
  `Collision` in `L`, which `cap_binding` already charges. A3′'s attack needs `cur_r` chosen after
  ζ; under (β′) that choice is made before ζ, and the attacker's 871-bit freedom becomes a
  ≤ 870-root event at a fresh squeeze.
- **The ε claim is right**: the certificate's per-fresh-query law is `(μ + εD)·2^256` with the
  single-squeeze count `N = 239·2^128 ≤ 2^256·deltaR` (`FRSoundnessCoreTail.N_le`,
  `FRSoundness4TailStep.kstate_step`). The two new squeezes escape in ≤ 870 and ≤ 1,535 answers
  (`chKEquiv : Digest ≃ K`, so counts are exact), which is `2^-245`, not a new maximum. `εR`,
  `deltaR`, `logCap`, `badCount` and `claim.json` do not move.
- **Two majors, both in the briefs, not in the construction.** PB-M1: the doom table "`DT 53 :=
  D_ζ`, `DT 55 := D_z`" cannot be taken literally — `hsingle` counts escapes `Dk₅₂ ∧ ¬Dk₅₃`, and
  with `Dk₅₃ = D_ζ` every answer escapes. The dooms at 52–55 must carry `DPf ∧ truthCap` and gate
  the ζ-clause on `A`'s honesty; the exact chain is written out in PB-M1. PB-M2: lever L2's scope
  is understated — `cap₄` is absorbed at **C.3**, before Q.3, so stream positions move from level 3
  on, not "after Q.4"; and the 4.x ladder is tied to 3.x's (`itemsOf_seq3 = items`,
  `FRShape4.lean:312`), so L2 either re-pins 3.x's `items_length`/`streamBytes_eq`/`piSize` and
  the 31 modules on `lvlStar`, or decouples `seq3` from `ladderOfR` first.
- Fourteen minors: literal slips (`f < 19` in `reloc`, `posW4`'s `+ 3`, the item numbers of `D`
  and `A`, a doubled field offset), the N8 headroom (484 blocks, not 256; L1 alone is over by 256
  and L2 alone by 512: both are needed), ΔS without the parent's template cost, stale §0/§8 text
  (ζ "from κ_c", "7 slots stays the fallback"), the build order's silence on A1′ and B0, and two
  simpler variants worth a line.
- **Verdict: adopt with fixes** (§5). The construction stands; the A2″ and A3′ briefs need the
  corrections below before they are issued.

## 1. What fixes what, from the code (the mistake §3.3 made, not repeated)

The chain is `fsItems4 = (itemsOf seq4).filter Item.isFS` (`FRSoundness4Pos.lean:36`), and
`Item.isFS` is false exactly for `.col` and `.node` (`FRTranscriptDefs.lean:274`). A squeeze answer
is the oracle's answer to `squeezeQ (lastAns es)` (`ext1`, `FRSoundnessCoreDefs.lean:43`), and an
absorb's query is `tagAbs ‖ st ‖ msg` with the whole message (`absorbQ`, `FRTranscriptDefs.lean:308`;
`msgAt` from byte 40). So a value is "fixed before squeeze s" iff it is a function of the chain
entries before `s`; a value V reads from π with `piField`/`piDigest`/`piElem` is chain-fixed only
if an earlier absorb carried the same π bytes.

| Value in (I)/(II) or a per-position check | Where V gets it (A2′'s code / §11.4) | Chain status under (β′) |
|---|---|---|
| kind (`sib_κ`, `logN`, `per`) | seed, byte 71 (`kindOfC`, `FRSoundness4Pos.lean:150`) | entry 0 |
| `cap[k]`, all 1,408 (1,536) entries | `piElem fCaps (32k)` (`capEntryOps`, `FRVIRFinals4.lean:679`) | absorbed by `cap0` and `C.0 … C.3` (`levelPhases`: level `i`'s `C` absorbs `cap_{i+1}`), before every P2 |
| `j_r` (position bits) → `k_r = j_r >>> sib_κ` | `.idx` on `ans.getD (p / K.per)` (`posOps4`, `FRVIR4.lean:138`), `shrN b K.sib` | P2.i's answers (`qPos`, `FRSoundness4TailTruths.lean:158`) |
| `D_r` | `piDigest` at `fieldOff fD + 32r` (static, §11.4 item 4) | **absorbed at FS 482 (`CapD`)**: `absorbOps` reads the same π bytes (`FRVIR.lean:714`) |
| `ζ` | `chK` of phase 53's answer | FS 483, after `D` |
| `A_k` | `piElemK fA (32k)` | **absorbed at FS 484 (`CapChk`)**, after ζ |
| `z` | `chK` of phase 55's answer | FS 485, after `A` |
| `z^{2^t}`, `z^{off_i}`, `ζ^r` | computed (`head`, `capReadOps`, `capEntryOps`) | functions of ζ, z |
| column, siblings | `piField`/`piDigest` from `fCols`/`fSibs` (`posOps4`, `merkleOps4`) | **not chain values**; bound to `D_r` by `assertEq cur_r D_r` through `askCol`/`askNode` in `L` |
| `cur_r` | the Merkle steps' last `keep` (`curOfY`, `FRVIR4.lean:149`); dummy depths `h ≥ K.sib` keep `cur` and assert the sibling zero (`merkleOps4`'s `act`) | the kind's own root, for every kind, at every one of `Σ tᵢ = 871` positions (`LadderFits` makes `t` equal across ladders, `FRShape4.lean:203`) |

So: ζ multiplies `D_r − cap[k_r]`, all three chain-fixed before 483; z multiplies `A_k − Σ_{k_r = k} ζ^r`,
chain-fixed before 485. The stream order (Q.i before P3.i) is irrelevant to this table, which is
what §3.3 and the first review got wrong.

## 2. Soundness of (β′): attacks tried

1. **A3′'s attack replayed.** Two openings per read with roots `d_r⁰ ≠ d_r¹`, choose `b_r` after
   ζ. Under (β′) V asserts `cur_r = D_r` where `D_r` was absorbed before ζ; the opening with
   root `≠ D_r` fails the assert. Opening both roots to the same `D_r` is `Collision L`
   (`FRMerkle.lean:88`), under which `cap_binding` (`:137`) fixes the column as
   `colL L D_r sib j`. The GF(2)-linear system has no unknowns left.
2. **Choose `D` to make (I) hold for the ζ that comes.** With `A` honest, (I) ⇔
   `Σ_r ζ^r (D_r − cap[k_r]) = 0` per F half (`mulKF` is K×F→K; coefficients in `F ⊂ K`, degree
   ≤ 870 in `ζ ∈ K`). Identically zero iff every coefficient is zero, i.e. `truthCap`. Otherwise
   ≤ 870 roots in K; `chK` is a bijection, so ≤ 870 answers. Retrying with a new `D` is a new
   fresh query, charged `εD` by `kstate_step`; `logCap = 2^96` retries are inside `εR`.
3. **Dishonest `A` to satisfy (I) with a bad `D`.** (I) is two K equations in 1,408 K unknowns:
   trivially solvable. (II) then is a nonzero polynomial in z of degree < 1,408 (1,536) with
   coefficients `A_k − Σ_{k_r = k} ζ^r`, all fixed before z: ≤ 1,407 (1,535) answers. Both dooms
   must be avoided at once; the chain in PB-M1 makes that the certificate's statement.
4. **ζ = 0, repeated positions, duplicate `k`.** `ζ = 0` is one of the ≤ 870 roots. Duplicate
   positions give two reads with the same `k_r`; honest `A_k` sums both powers; (I)/(II) do not
   care. Characteristic 2 cancels nothing: the coefficient vectors are compared entrywise.
5. **Kind confusion.** `sib_κ`, `logN`, `per` come from the seed byte; the group program's
   `posOpsG` uses them per index; `D` has 871 entries in the same order for every kind (`t` equal
   across ladders), so `r` is kind-independent and `A`'s offsets `off_i` are the same for every
   kind (caps are equal per level across ladders).
6. **Order of `L` versus the stream.** The prover may put the `CapD` absorb before its node
   queries in `L`; then an answer later in `L` is carried by an earlier query: `Hit`, which is
   `Bad L` and charged by the Hide potential (`badCount`, `FRLog.lean:192`). `carried` for an
   absorb is every 32-byte element (`FRTranscriptDefs.lean:373`), so the 871 digests of `D` are
   carried; the per-query window bound `length_wins_le ≤ 2^17` (`FRLog.lean:90`) holds for any
   query under 2^21 bytes; `D`'s query is 27,912 B and `A`'s 49,192 B, both under the service's
   2^20-byte cap (PROVER.md §5, Q13).
7. **Other π reads used as committed.** The finals' `capChkOps` read only `fA`, `fCaps` and (after
   §11.4) the `D` registers; the positions read `fCols`, `fSibs`, `fD`. The statement, round
   messages, the final message and the caps are all absorbed. Nothing else.

**ε, recomputed with the certificate's law.** `PhaseObl.hsingle` demands the escape count at a
single squeeze `≤ N`, and `kstate_step` needs `N ≤ 2^256·deltaR` (`FRSoundness4TailStep.lean:651,
671`); `N = 239·2^128` is proved (`N_le`), `deltaR = epsD − 2^-142`, `epsD = epsR − epsH`,
`epsH = 2^-142 + 2^-238`, `epsR = 15/2^124 = 240·2^128/2^256` (`FRSoundnessCoreSteps.lean:76–86`).
Phases 53 and 55 are single squeezes (`fsRnd4 = none`), their counts 870 and 1,535 are ≤ N by
≈ 2^125. No constant moves. P3.4 returns to its 3.x shape (ζ is no longer its first answer), which
removes A2′'s `hround` complication there. **Confirmed: `εR` and `claim.json` unchanged.**

## 3. Findings

### PB-M1 — the doom table at phases 52–55 must be the carried disjunction, not `D_ζ`/`D_z`

§11.1's table and §11.5 say "`DT 53 := D_ζ`, `DT 55 := D_z`, `DT 52`/`DT 54` carry no doom".
Read literally against `PhaseObl` (`FRSoundness4TailStep.lean:651`):

- `hsingle` at 53 counts `{a : DT 52 (es) ∧ ¬ DT 53 (ext1 es a)}`. With `DT 53 = D_ζ` (a rare
  event) and `DT 52 = DPf` (or anything carried), **almost every answer escapes**: the count is
  ≈ 2^256, not 870.
- `habs` at 52 needs `DT 51 L es → Rej ∨ DT 52 L (es ++ [x])`; "no doom" at 52 fails it unless
  `DT 52` carries `DPf`.
- The final obligation needs `accept → ¬ DT 55`; `¬ D_z` alone says nothing about `DPf`.

The chain that satisfies all five obligations and the final case split (I checked each):

```
DT 52 := DPf ∨ ¬truthCap                                           -- habs from DT 51 = DPf
DT 53 := (DPf ∧ truthCap) ∨ (¬truthCap ∧ Σ_r ζ^r (D_r − cap[k_r]) ≠ 0)   -- escape ⊆ D_ζ: ≤ 870
DT 54 := (DPf ∧ truthCap) ∨ (A = Â(ζ) ∧ ¬truthCap ∧ Σ ≠ 0) ∨ A ≠ Â(ζ)     -- habs by cases on A
DT 55 := (DPf ∧ truthCap) ∨ (A = Â(ζ) ∧ ¬truthCap ∧ Σ ≠ 0) ∨ (A ≠ Â(ζ) ∧ ¬(II))  -- escape ⊆ D_z: ≤ 1,535
```

with `Â(ζ)_k := Σ_{r : off + k_r = k} ζ^r`, `Σ` the two F-half sums, and `(II)` the z identity;
all of `truthCap`, `Σ`, `Â`, `(II)` are functions of `es` alone (so `hstab` is trivial for the new
clauses). Final split under `accept` (which gives (I), (II), and `openPath … = some D_r` at every
position from `cols4_of_run`): (II) refutes the third disjunct; `A = Â ∧ (I)` gives `Σ = 0` and
refutes the second; `truthCap` with the position facts gives today's `openPath … = capDig …`,
hence `cols`, hence `¬DPf` by the unchanged 3.x argument — refuting the first. §11.1's phrase "the
Pf doom's background hypothesis `truthCap`" is this first disjunct; the brief must say so
explicitly, and the A3′ definition of done must name `D_ζ`/`D_z` as the *escape sets* of the
rows, not as the dooms. **Fix:** replace the table's "Statement" column and §11.5's `DT`
assignments by the chain above (or an equivalent one), and add `habs` at 52/54 and the final
split to A3′'s obligations.

### PB-M2 — lever L2 moves more than "level 4 and later", and touches 3.x's ladder

(a) **`cap₄` is absorbed at C.3, not at level 4.** `levelPhases i` absorbs `capBytes i =
2^(lvlStar (i+1)).cap·32` in level `i`'s `C` phase (`FRTranscriptDefs.lean:219–231`; `phasesOf`
likewise, `FRShape4.lean:278`). Level 3's `C` phase (number 42) precedes P2.3, **Q.3** (132
positions × 7 items), P3.3, P1.4, C.4, P2.4 and Q.4. So in the stream, every byte from C.3's
payload end moves by +4,096; in π, `fCaps` grows by 4,096 and `fFinal`, `fCols`, `fSibs`, `fD`,
`fA` all shift; `fSibs` shrinks by 126·32 at its level-4 part. "Positions after Q.4 move" (§11.2
L2 row, §11.4 item 7 "R4/P4's level-4 position lemmas") must read "stream positions from C.3's
payload on; π offsets from `fFinal` on; level-3 *and* level-4 position lemmas". The FS entry
indices do not move (correct), but the C.3 item's `len` changes, so `fsItems4` changes content and
every `decide +kernel` over it re-runs. §5.1's arena₂ stride `S₄ = 57` becomes 50 (22 + 4·7) and
its FS count 468 becomes 486.

(b) **The 4.x ladder is tied to 3.x's.** `itemsOf_seq3 : itemsOf seq3 = items` is proved by
`seq3.lv = lvlStar` (`FRShape4.lean:312–315`), where `seq3.lv = ladderOfR 6 32` and `lvlStar =
ladder32`. Changing level 4's cap in `ladderOfR` (`FRShape4.lean:176`, the definition `CKind.lv`,
`lvOf`, `Seq.lvK` all read) forces the same change in `ladder32`/`ladder30`
(`FRTranscriptDefs.lean:90–95`), which changes 3.x's `posItems`, hence `items_length = 8891`,
`fsItems_length` (no), `streamBytes_eq = 1481344`, `fieldSizes`, `piSize`, and the 3.x position
lemmas in the 31 modules that use `ladder32`/`lvlStar` (S-H's `FRX` tape facts included). §11.4
item 9's "untouched from A2′: the 3.x modules" is false under L2. Either (i) accept the 3.x re-pin
(and note that RET is retiring those modules anyway), or (ii) give `Seq` a `cap4` field (default
7; `seq4`: 8) threaded into `ladderOfR`, keep `seq3` at 7, and re-point `CKind.lv` from
`lvOf κ.m` to `seq4.lvK κ.m`. Both are more than "literals and one definition"; the brief must
choose. Also missing from §11.4 item 7: `ladderOfR` itself (the `m = 31` ladder, `ladderOf 31`
level 4 `⟨4, 11, 126, 7⟩ → cap 8, sib 3`), `ladder_sq_sib`, `ladder_sib`, `seg_ladder_fits`,
`node_ladder_fits`, `FRNodeRead4`'s `segTr_length`/`slotTr4_length` (8,907 → 8,783) and
`FRX4Prog.szPs`/`FRX4Ext` (|π| → 875,312), all of which §3.4 listed for (β) and §11.4 dropped.

(c) The ε side of L2 is clean: Merkle binding is depth-independent (`cap_binding` over `ss.length`),
the proximity parameters (`ell`, `logN`, `t`) do not change, and the C.3 absorb's 256 carried
digests are far under the window bound. The decoder (`FRXDec4Lv`/`Level`) takes `CKind.lv κ i`
as a parameter and reads `sib` only through `colL`: `lv_params` re-runs, no statement changes.

### Minors

**PB-m1 — `reloc`'s `f < 19`.** `FRVIR4Mux.lean:183–184` relocates `piDigest`/`piDigestAt`
(and the `piElem` cases nearby) only for `f < 19`; with `nFields4 := 20` and `fA := 19`,
`capEntryOps`' `piElemK fA (32k)` falls into the `else` branch and resolves field 19 with
`evalOp`'s 3.x table, which has no field 19. Honest proofs fail the KAT. Add the literal to §11.4
item 1 (and `fieldOffs`' `List.range 19`).

**PB-m2 — `posW4 S i := 4 + 6·sib + 3` is off by one.** Registers of a position: `idx`,
`piField`, `askCol`, `dotKF` (4), six per Merkle step, `shrN` (1), `piDigest` (1); `assertEq`
writes no register (`stmtOps4`'s layout, `FRVIR4.lean:85–90`, has `piField` at `b + 2` right
after an `assertEq`). So `posW4 = 4 + 6·sib + 2`, the `D` register `b + 4 + 6·sib + 1` as the memo
says, and `ysOf fi i` stays at `+ 3`. A wrong `posW4` misaligns every later position's base.

**PB-m3 — `D`'s and `A`'s item numbers collide.** §11.4 item 6 puts `D` at "item 8,781" and `A`
at "8,783 − 2 = 8,781". With 8,783 items (0-based last index 8,782 = the z squeeze): `D` 8,779,
ζ 8,780, `A` 8,781, z 8,782.

**PB-m4 — a doubled field offset.** §11.4 item 4 writes `.piDigest fD (dO + 32·p)` with `dO :=
fieldOff fD + …`; `posOps4` addresses π absolutely through field 0 (`.piField 0 (co + …)`), and
`reloc` adds the field's offset for `f < 19`. Write `.piDigest 0 (dO + 32·p)` with `dO` absolute,
or `.piDigest fD (32·(Σ_{i'<i} t_{i'} + p))`.

**PB-m5 — N8's headroom and the levers' independence.** Recomputed (`recompute.py`): A2′
`hUsed 193,208 / lBase 193,280`; (β′) alone `196,712 / 196,864` (over by 1,280, as A3′ said);
(β′)+L1 `195,836 / 195,840` (**over by 256**); (β′)+L2 `195,968 / 196,096` (**over by 512**);
(β′)+L1+L2 `195,092 / 195,328` (fits). So **both levers are needed, and neither alone suffices**
— §11.2 should say so. The headroom is `195,584 − 8 − 195,092 = 484` blocks of `hUsed`
(`hEnd ≤ lBase`, `hEnd_le`), not 256: 256 is the `lBase` granularity. L1+L3 would also fit
(`195,392`, `lBase` exactly 195,584) at a worse |π| (+10,688 B), so L2 is the right choice.

**PB-m6 — ΔS omits the parent's template cost and miscounts slots.** §11.3's +0.15 s is
+0.058 (|π|) + 0.058 (V's own 9 ms VM) + 0.03 (prover). §11.7's ≈ 2 ms VM per prototype × 2
prototypes ≈ 4.2 ms runner ≈ +0.03 s is a V cost of every node and belongs in the same ΔS:
≈ +0.18 s. "(4 per node)" in §11.7's total row: N4 has 5 verifier slots and N8 has 8; if the
figure is per *prototype* (once per key set), say so and drop the "per node" count.

**PB-m7 — `N_M/1.05 = 7,990,232`.** `2^23/1.05 = 7,989,150`. The ratio is 1.0349 either way;
fix the literal (it is also §6.1's "7.99 M").

**PB-m8 — stale text that now contradicts §11.** §0 item 3 still describes (β) with "the
transcript's last `κ_c` as ζ" and `A ∈ K^1920`; §0 item 9 and §8 still say "N8 with 7 slots … stays
the fallback", where §11.2 rejects L4 ("not available: it fails step 1"). §11.6 lists what is to
be re-read with §11's constants but not §0 or §8. Mark them.

**PB-m9 — L4's numbers are right; the wording of the consequence is not.** Density ∝ 1/n² on
[2^17, 2^20]: `P(n > 3·2^18) = (1/3)/7 = 1/21 = 4.76 %` (discrete sum: 4.7619 %); both chains:
`1/441 = 0.227 %`. "A failed step 1 loses the stream" understates it: a non-zero exit or a missing
`proof.bin` **fails the run, and "the first failure ends the evaluation"** (PROVER.md §5). The
rejection stands on that rule; cite it.

**PB-m10 — "4d5700c's V is certified" and "rev44 should sit at 4d5700c's V".** The chain at
`4d5700c` has the residuals of `ks_rev4`/`certificate_rev4` open (QUEUE.md "The residuals …: the
whole remaining soundness work"); what is true is that its S-G tail builds with the per-position
`cols`. And A2″ should start from A2′'s tree (`f853d37`/`ccdde20`: the fields, phases,
`capChkOps` and ops are reused; §11.4 is a delta on it), so a revert-then-reapply on `v4/rev44`
is churn; the QUEUE's "paused, V unsound" marking is the right state until A2″ lands. Say "A2″
re-issues A2′ on A2′'s tree; the branch stays paused and marked".

**PB-m11 — the build order omits A1′ and B0's landing.** §11.2's stride 24,222 and
`aggL 4 = 4·24,222 − 2` presuppose R-A′'s spacers (A1′), which `FRNodeKinds4.aggB` at `ccdde20`
does not have (`1 + k·(segB − 1)`); without them `aggL 4 = 96,880`, 6 blocks less — the fit
holds either way, but A1′ and A2″ both edit `FRNodeKinds4`/`FRNodeLayout4` literals and must be
sequenced. B0 is "held uncommitted" with its own `FRNodeRows4Hint`; §11.7 says B2′ regenerates
the hint but not that B0 lands first. Add both to "Who builds what".

**PB-m12 — `attack_neg` as described is a V-run control, not a replay of A3′'s attack.** Under
(β′) the attack cannot be *expressed* in a log (the attacker's choice of `D` after ζ is not a
chain). The control that carries the counterexample is at the doom level: a log with `D_r ≠
cap[k_r]` at one read and the honest `A`, where (I) holds at ζ only if ζ is a root — `dZeta_ctl`
is that control, and a `dZeta_neg` (a non-root ζ makes (I) fail) completes it. Keep `attack_neg`
(two openings of one read, roots `d⁰ ≠ d¹`, `D_r = d⁰`: the run of the `d¹` opening fails the
assert) but state what it shows.

**PB-m13 — `D_z`'s degree is given as both 1,407 and 1,535.** §11.1's table (pre-L2) says
≤ 1,407, §11.5 says 1,535 (post-L2). State one, with "(1,407 without L2)".

**PB-m14 — two variants worth a line in §11.1's alternatives.** (i) Absorb the *computed* `cur_r`
registers instead of a π field: a new op (absorb-from-registers) in `ir.rs`/`OpImpl`/`absorbOps`,
no per-position assert (the pack map binds the template's `cur` to the absorb payload cells, the
same 2 rows), |π| −27,872 B (≈ −0.02 s of S), the stream unchanged; against §11.4 item 9's "all
existing op kinds". (ii) Place `CapD` between Q.4 and P3.4 and reuse P3.4's first answer as ζ (it
then *is* after `D`): saves the ζ squeeze (80 B per segment, 10 blocks for N8) and one `hsingle`
row, at the cost of shifting FS entries 463–481 by one (L2 already moves the stream positions
there). Neither changes the soundness argument; both are small. The brief's "make Q.i chain
items" is not available: a Merkle node query cannot carry the sponge state (the tree is committed
before the queries), and absorbing the openings instead is +8,437 absorb items ≈ +675 KB of stream
per segment (+29 %): N8 ✗ by a wide margin. (β′)'s `D` is the minimal binding.

## 4. The brief's questions

1. **Soundness.** Every summand fixed before its challenge (§1); V checks every read at every
   level and position, dummy depths included (`merkleOps4`'s `keep`/`assertZero`; no dummy
   positions exist since `t` is equal across ladders); `k_r` from P2.i; the dooms fit `εR` with
   `claim.json` unchanged (§2). No other π-read value is used as committed. The doom *table* must
   be restated (PB-M1).
2. **L1.** Verified: `nodeLayout4` has exactly `wotsIvs κ 0 ++ wotsIvs κ 1` (`FRNodeKinds4.lean:129`),
   `mir4_fits` and every `mirB4` use are at `σ < 2` (`FRNodeTarget4`, `FRVerifierImplNode4`'s
   `EM0`/`EM1`, `FRSoundness4P4aNS`), `wmSlot4 = 146 = ⌈581/4⌉` (`Layout.mirSources`). The reclaimed
   `[wmB κ 2, hUsedN κ − 8)` is `.free` with no target for every kind; S-E13b's cells 8704–11648
   are L cells (`Lc κ σ (8704 + t)`, `FRNodeRows4Wots.lean:99`), not H. N8 −876, N4 −438, N2
   −146 are right. Adopt.
3. **L2.** The arithmetic is right (−126 × 112 + 4,096 + 4,096 − 32 = −5,952 → 1,550,080 =
   64·24,220; |π| 875,312; items 8,783; qV 35,135; `hUsed` 195,092). The scope is wrong (PB-M2):
   C.3 moves, 3.x's ladder is tied, `ladderOfR`/`m = 31` and the dropped literals. ε: none.
4. **L4.** 4.8 % / 0.23 % recomputed exactly (1/21, 1/441); the consequence is "ends the
   evaluation" (PB-m9). Rejection justified and moot (L1+L2 fit).
5. **Templates and N8.** Row counts check: 2,613 + 4,608 + 33 + 23,517 + 7,839 + 4,355 + 7,680 +
   1,748 = 52,393. Segment slot 965,008 (92.0 %), region A 927,528 (88.5 %), N8 7,720,064 against
   7,989,150: 1.0349× (PB-m7). The V prices (0.1/0/0.3/0.4/1.2 ms) are estimates consistent with
   §6.2's lookup pricing; they are not measurements and should be labelled so until B2′ measures.
6. **Build order.** A2″ → (B2′ ∥ A3′) → P2 is right in its dependencies; A1′ and B0's landing
   are missing (PB-m11). `attack_neg` is in §11.5's done; its form needs stating (PB-m12).
   "Sit at 4d5700c's V": unnecessary churn, and "certified" overstates (PB-m10).
7. **Simpler.** Q.i as chain items is not available; two small variants in PB-m14.

## 5. Verdict

**Adopt with fixes.** (β′) is the right repair: it binds exactly the value A3′ exploited, at the
earliest point the chain can carry it, with no new lemma family and no change to any ε constant.
Before the A2″ and A3′ briefs are issued: write the doom chain of PB-M1 into §11.1/§11.5 and A3′'s
definition of done; correct L2's scope per PB-M2 and decide the 3.x ladder question; and apply the
literal fixes PB-m1 … PB-m4, which an implementer would otherwise discover one build at a time.
The remaining minors are text.
