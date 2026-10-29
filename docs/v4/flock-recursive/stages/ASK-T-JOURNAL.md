# ASK-T journal

Track ASK-T (the ask templates: `ATAsk` for every ask). Worktree rev44, HEAD 74a2528. Build tree
`logs/fr-build-ASKT` (copy of fr-build-ASKP; MINE.txt = my modules). Logs `logs/ASKT/`.

## 2026-10-29

- Read ASK-P/IMP/SRA/B3 RESULTs, PACK-4.4 §1.3/§4.2, FRNodeRun4, AskPos*, PackSound, FRVIR4 generators.
- Tree copied, snapshot onto 74a2528 (no MINE yet).
- Design: generator `askTGT X π` (low module), per ask k (k < 8,783 from tables):
  check `op.item? = itemsOf[k]`; byte operand (seed hdr / absorb msg / col) checked against a per-item
  source table (absolute offset, length, query offset) and `pre = piField`, `m + 1 = size`;
  digest operands (absorb/squeeze state, node halves) tied to arena₁ elements (per kind, act-gated
  when not uniform); seed's vk/c elements 1–4 tied to IMP's `input` cells; answer cells tied to
  arena₁ `ansE k`. Tags: no rows, the existing pack pins (`pins_of`: `wfSeg`, `HeadOk`). Message bytes:
  no rows, `reassemble4` positional spec (π is reassembled from the same trace).
  Last item (CapChkZ squeeze, in the last block): bridge generalised with `AggPad4` (whole last block).
- Generator `FRNodeRows4AskT` (`askTGT`, tables `itemsT`/`srcT`/`offT`, `srcOf`); probe `asktcnt`
  (`logs/ASKT/asktcnt.log`): proto 0 55,212 rows, proto 1 62,180, **0 failing rows** (every check passes
  on the honest compile), 10,452 / 20,904 gated (kind-varying Merkle depths).
- `FRNodeRows4AskTB` (tables, `src_spec`), `FRNodeRows4AskTH` (`slot_byte'` by `AggPad4`: the last
  item covered; `tag_byte`), `FRNodeRows4AskTS` (**`atAsk_T`**) compile, no sorry.
- Orchestrator: CK committed 44a4975 (proto 0 +6,720 rows); re-snapshot before final build.
- FRNodeRows4: import + `askTG := ((askTGT ..).add inpTG).add rsvTG`. AskPosF: `withRsv_none`/`askFold_rsv`
  (no users) replaced by `askAq`, `withRsv_askT`, `askFold_askT`. New `FRNodeRun4AskT`: `atOk_askT`,
  **`gap4Imp_of_askT`**, controls. Full build started at 44a4975 + mine.
- Build #1 red: FRNodeRows4Plan `protoV4_eq` hit max recursion (elaborator unfolding `itemsOf seq4` via
  the tables reached through `askTG`). Fix: `@[irreducible]` on `itemsT`/`srcT`/`offT`; `offT_get` by
  `unfold offT itOff`. Build #3 green at 44a4975 + mine (2,664 jobs, 0 sorry). Axioms 31 decls OK incl.
  `certified`; source rule 447 files 0 findings.
- Probes at 44a4975: asktcnt 55,212 / 62,180 rows, 0 failing; artime: inR true, askV 61 ms per prototype
  (was 3.6 ms); V(N4) A/B vs ASK-P's binary: best 276.4 → 417.5 ms (own kind), 323.1 → 455.5 (all kinds).
- Orchestrator: IMPC committed 87519f4: askTG gains `.add (impcTG (XofT π) π (provL 0 (protoProg π).ops))`
  (import FRNodeRows4AskI). AskPosF: dropped withRsv_askT/askFold_askT (can't name withImpc there);
  IMPC's controls restated at `askAq`: `withImpc_askT` (AskIS, askTGI := askTG), `withImpcC_askT` (AskIR).
  FRNodeRun4AskT: `askFold_askT` (withImpc askAq), `gap4Imp_of_askT` via IMPC's `gap4Imp_of_impc`.
  Re-snapshot onto 87519f4; build #4 running. bitOf-through-SlotRunA (IMPC item 3): listed open.
- Build at 87519f4 + IMPC fold: V's process start crashed (stack overflow): IMPC's `provL` is non-tail
  recursive over ~155k ops. Added `provLT` (tail-recursive) + `provLT_eq` in FRNodeRows4AskI; askTG,
  `withImpc`, `pvP` use it. Duplicate `slotIn_π` (IMPC has one) removed from mine.
- Final build green (5,029 jobs incl. probes, 0 sorry); axioms 35 decls OK; source rule 449 files 0.
- plan4t init 7.35–7.56 s user (ASK-P bin 6.18–6.54); asktinit: my generator +0.12 s, impcTG +0.40 s.
  V(N4) best 274.9 → 444.6 ms (own), 320.6 → 488.9 (all) vs ASK-P bin; artime askV 61 ms/prototype.
  MxKat PASS. Kernel: new modules ≈ 3.3 s type checking, off `certified`'s path.
- RESULT written. Open: V levers, impcTG start cost, Gaps4 routing, bitOf via SlotRunA.
