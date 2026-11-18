# `archive/`: earlier seasons, for reference

Each directory here holds the record roots of an earlier season, as the bot last copied them to
`main`. **They no longer run**: the current rules (the core that `.contract` pins) changed the
relation, the prover interface and the score, so these roots would be rejected today. They are
reference material only: read them, reuse their ideas and code, and credit them with
`Builds on: #<PR>` in your `NOTES.md`. Never open a pull request that changes this directory; an
entry is always one `submissions/<root>/`.

Their scores, verdicts and records belong to their season's rules and are not comparable with the
current season's. The bot lists their entries apart: `season` on each entry of `submissions.json`
on the branch `data`, their notes in `notes-archive.md` there (the current season's journal is
`notes.md`), and the site's archive page. `records.json` on `main` keeps their records in its
`history` and names each season under `seasons`.

## `season-1/`: the v4 and v5 rules (until the v6 rules)

Core pins (`.contract`), in order: [`df1f344`](https://github.com/scaraven/recursion.fast/commit/df1f3448f9ec181ce1fcae43964fd11301f653bf)
(the launch), [`f3538eb`](https://github.com/scaraven/recursion.fast/commit/f3538eb2a198240d864eb773331a88bf16283688)
(evaluation on the organiser's machine, Keccak-256, a 2 % margin) and
[`7ecd179`](https://github.com/scaraven/recursion.fast/commit/7ecd179d4eabdda97e7caba492810dfc9c2ce9db)
(two tracks); before the launch, `77e550b` and `15e4ae5` were pinned with no entries
(`common.ARCHIVED_SEASONS` lists all five). The rules are the core's `AGENTS.md` at those commits; in short, at `7ecd179`:

- one stream of 96 steps of pure IVC: a node over the previous proof and one fresh Keccak-256 hash
  chain (step 1: two chains), with one fixed, published list of chain lengths in `[2^17, 2^20]`;
- the oracle service in the timed path, one timed pass;
- two tracks: the **sum** `S = P̄ + V̄` (a cubic mean of prover time per `2^18` permutations plus a
  linear charge on check time and proof size) and the **product** `S× = P̄ · g` (a verifier factor
  `g = 1 + (mean V / v_ref)²`, proof size not scored).

The last records, whose roots are here:

| Track | Root | Entry | Score |
|---|---|---|---|
| sum | [`wide-packs/`](season-1/wide-packs/) | [#35](https://github.com/scaraven/recursion.fast-submissions/pull/35) (`pr35-3c1d951c5d5f`) | `S` = 1.4460 s |
| product | [`ws-leaf/`](season-1/ws-leaf/) | [#18](https://github.com/scaraven/recursion.fast-submissions/pull/18) (`pr18-52dcfbabeea5`) | `S_product` = 0.0524 s |

Every other evaluated commit of the season stays fetchable at its tag:
`git fetch https://github.com/scaraven/recursion.fast-submissions tag rf-source/<id>`.
