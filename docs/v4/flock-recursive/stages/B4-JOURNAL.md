# B4 (track L-circ): JOURNAL — `aggChk` from the node rows

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `e464756`). Build tree
`logs/fr-build-B4` (copy of `fr-build-A1`; `MINE.txt`; `scaffold/apply.sh` + `scaffold/autostub.sh`
stub HEAD's red RSV-S declarations in the tree's copies only). Logs `logs/B4/`.

## 0. Design (2026-10-29)

`Gap4R.aggChk a`: `∃ vs, mapM segView (aggSegs …) = some vs ∧ aggChecks (stOf c₁ c₂ σ) n e vs`, with
`π_A = aggHdr k hAn hAe ++ slot proofs` (`rd4`). The pieces and where each comes from:

| check | source |
|---|---|
| `segView` of each sub-slot proof is `some` | `kindS` (pack rows, A1′), refactored out of `gap4_of_rows` as `kindS_of_rows` |
| `c = leafStmt e n` | **no row**: Z truth at `cAB` (`hashA` target) + `hashA_leafStmt` + `PubCells4` (`stC = hc cAB 2/3`) |
| `1 ≤ k ≤ 4` | `actK_kAct` |
| `1 ≤ nᵢ ≤ cap κᵢ` | **rows**: range rows on `E15ᵢ`'s bits 8–71, gated by `Sᵢ` and the kind selectors |
| `Σ nᵢ = n` | **rows**: masks `Sᵢ·bit`, ripple-carry adder (char 2: sum = `a+b+c`, carry = `ab + (a+b)c`), final packed compare with `A6`'s bits 8–71 |
| `e_k = e` | **rows**: `ind j`-gated compares of `E13/E14/E15` (sub-slot `j−1`) with `A4/A5/A6` (`cAB`'s message) |
| chaining `s_{i+1} = h_i` | **rows**: `S_{i+1}`-gated byte-shift rows `E6/E7` of `i+1` = packed bits of `E13/14/15` of `i` |

Stream geometry (segment-relative, A.5): `hdr` = seed query bytes 71–118 = stream bytes 80–127
(elements 5–7; `start` = elements 6, 7); `stmt` = item 1 (`absorb 128`) message = stream bytes
208–335 (elements 13–20); the view's `h` = stmt bytes 1–32 = stream 209–240 (E13[1..16) ‖ E14 ‖
E15[0]), `n` = stmt bytes 33–40 = E15[1..9). `hashA` block `cAB`'s message: A4 = hc cAB 4, A5, A6,
same byte layout (`tagLeaf ‖ e ‖ enc64 n`).

L cells: signed child `σ = aggChild a`'s stride, offsets from 12,288 (spC ends at 11,648; the
orchestrator's note). Bits `bC i u q` (`i < 4`, `u < 3`, 1,536), `aC` (256), masks, adder, aux:
2,200 cells.

`PfView pf` (new hypothesis next to `PfHdr`): bytes 16–47 of `pf (e₀ :: e₁ :: tr)` are `e₀`'s
query bytes 87–118 and bytes 49–88 are `e₁`'s query bytes 41–80 (A.5's `reassemble`: `hdr`,
`stmt`).

## 1. Log

- 17:02 tree created; HEAD's closure built green after stubbing `FRSoundness4R4FrE` (5),
  `FRSoundness4R4FrRS.e_bind4`, `FRSoundness4R4Start.start4_of_fields` (all RSV-S, red at HEAD).
- Orchestrator note: link region of slot 1 holds ≤ 16,831 rows; `spC` up to 11,648; `main_not_final2`
  — the end check must not rely on counters (it does not: it is gated by `ind j` from the
  activities, and the end compare reads the views' bytes, not the chain's counters).
- 17:10–18:30 built: `FRNodeRows4AggChk` (cells, rows, length bound 2,076/aggregate), the fold
  (`FRNodeRows4Ext.xRowsA`/`chkRows`, `FRNodeRows4.xRowsK_eq` → `xRowsA`, literals 7,904 → 12,056),
  `FRNodeRows4AggChkB` (bits/bytes/numbers, full adder), `FRNodeRows4AggChkS` (chain/end/range/sum
  from the rows), `FRNodeRows4AggChkG` (`PfView`, `view_sub`, `stmt_A`, `aggChecks_of`,
  **`aggChk_of_rows`**, **`gap4_of_rowsI`**). `FRNodeRows4PackSound`: `kindS_of_rows` factored out of
  `gap4_of_rows` (no statement change), `wots_aggPad_of_rows`'s membership through `xRowsA`.
  All check green module by module. WIP sorries were kept in the build tree's copy only.
- Next: controls, `PfView` for `reassemble4`, full build, axioms, source rule, CPU, V(N4)/V(N8).
- 18:00 `PfView` restated over the whole `hdr` (bytes 0–47) and `stmt` (48–175) fields (A.5's
  form; the view uses `hdr.pub` and `stmt[1..41)`). Controls module green. Axioms (58, no
  `sorryAx`), source rule (0 findings). `plan4t check`: `evalMT4` = sparse sum on N2/N4/N8
  (`equal true`). MxKat passes. CPU profiles in `logs/B4/cpu.txt`. Plan init 5.3–5.8 s user (A1′ 5.1).
- V(N4) A/B round 1 (4 × 21, load 16–21): too noisy; re-run with 6 rounds.
- Not done (context budget): ask templates (B3 `ATOk`, red at HEAD) and PK-m7's statement rows; both
  serve `imp`; designed in RESULT §6.
- 18:20 V(N4) 6-round A/B: +2.9 ms own kind, +6.9 ms all kinds; N8 proxy +9.1 ms. RESULT written.
