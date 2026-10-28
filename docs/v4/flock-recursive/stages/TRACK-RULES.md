# Rules for every track agent (orchestrator's standing instructions)

- **Spec.** `docs/v4/flock-recursive/BLUEPRINT.md` is normative; Appendix A pins the interfaces.
  The reviews (`reviews/BP-*-review.md`, including their Round 2 sections) say what is still moving.
  Where your track depends on an open finding, keep that part parametric and say so. Never edit the
  blueprint; report the changes you need in your RESULT.
- **Rules of the competition.** `AGENTS.md` and `CLAUDE.md` in the worktree. Briefly:
  - only the axioms `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`;
  - no `partial`, `unsafe`, `opaque`, and no code-changing attributes;
  - no elaboration-time code (the source rule also rejects words such as "macro", "syntax",
    "partial" in comments);
  - imports only from the allowlist, plus the entry's own `FR*` modules;
  - a positive and a negative control for every definition the certificate relies on;
  - a proof never changes the statement it proves.

  Check with `python3 -I .contract/scripts/source-rule.py submissions/flock-recursive` (or the pin's
  equivalent) before you finish.
- **Skills.** Use `lean4:lean4` and `lean-spec-authoring` for Lean work (load them with the Skill
  tool).
- **Files.** Modules are `submissions/flock-recursive/lean/FR*.lean`, in namespace `FR`. Write only
  the modules your track owns (the blueprint's §7 table). Never edit another track's modules: if you
  need a change in one, ask in your RESULT. `FRField*` belong to S-A and are final.
- **Building.**
  - Use your own build tree: copy `logs/fr-build/gen.sh` to `logs/fr-build-<track>/gen.sh`, run it
    there, and build only your targets (`lake build FRFoo FRBar`). Other tracks' unfinished modules
    must not break your build.
  - Packages come from the private tree `logs/pkgs`, via `logs/org`. Never write into other
    worktrees' trees or the shared package tree, and never run `lake update` or
    `lake exe cache get`.
  - Every build runs under `timeout`. If one runs much longer than expected, inspect it
    (`ps -eo pid,etime,cmd`, locks, Mathlib being rebuilt) and fix the cause. The VM has 32 cores
    shared by several agents, so don't start more than 2 parallel Lean processes.
- **Memory cap (mandatory, after the 2026-10-27 OOM).** A `lean` process reached 41.6 GB and the
  kernel's global OOM killer took down the server. Run every `lake`, `lean` and `cargo` command
  inside a capped scope:

  ```sh
  systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 -- timeout 1800 lake build FRFoo
  ```

  A runaway is then killed inside its own cgroup. If a build is killed there, restructure the
  proof; never raise the cap. Usual causes: `decide` or `simp` on a large concrete structure (a
  layout, a table, a program), or `rfl` unfolding a big definition. Use a checked certificate or a
  lemma about the generator instead. Avoid the lean-lsp MCP tools on large modules: the LSP server
  runs outside any cap. Prefer capped command-line builds.
- **Kernel cost.** The certificate must build in ≤ 600 s and kernel-check in ≤ 600 s on a 4-vCPU
  runner. Avoid `decide` on large terms. Use checked certificates (e.g. an inverse matrix) instead
  of enumeration. Log per-module wall and kernel time with **sequential** elaboration:
  `lean -DElab.async=false --profile …` on one core. With asynchronous elaboration, Lean's
  "type checking" figure includes kernel tasks waiting for the core, which inflated S-A's
  figure 2.5× (`reviews/S-A-golf.md`).
- **Pace.** Work through your item list in one invocation. Stop only when it is done, when you are blocked, or when your context is genuinely long. Each stop-and-resume re-reads context and costs more than it saves. The user's budget concern is the number of concurrent agents, not the size of a chunk.
- **No sub-agents.** Do not spawn subagents or forks of yourself (FR-D8: at most 3 agents run at once,
  counted by the orchestrator). If the work is too large, write a handover and stop.
- **Records.**
  - Keep a running `docs/v4/flock-recursive/stages/<stage>-JOURNAL.md`.
  - At the end, write `<stage>-RESULT.md`:
    - what was built, file by file, with code lines (loc);
    - build and kernel times, with logs under `logs/<stage>/`;
    - the controls, and what each shows;
    - deviations from the blueprint, with reasons;
    - open questions.
- **Git.** Do not commit and do not push; the orchestrator commits. Do not edit other repositories.
