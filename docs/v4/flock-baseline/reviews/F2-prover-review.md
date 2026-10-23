# F2 (native prover of `spartan-srom`): adversarial review, 2026-10-23

Reviewed: commit `f8f7c1e` on `v4/flock-baseline` (worktree `recursion.fast-submissions-v4`),
`submissions/spartan-srom/prover/` (every `.rs`, `build-asm.sh`, `sanitize-asm.py`, `selftest.py`,
`README.md`, `Cargo.toml`, the generated `prover.s`), the claims in
`docs/v4/flock-baseline/stages/F2-prover-RESULT.md`, the logs under `logs/f2/`. Read against:
`BLUEPRINT.md` §1, §2, §7; `recursion.fast-v4h/harness/{PROVER,FORMAT}.md`,
`service/PROTOCOL.md`, `harness/rfh/{prover,checks,files,signed,sandbox,bench}.py`; the Lean side
`lean/SpartanSromNode.lean`, `SpartanSromDecode.lean`, `SpartanSromVerifierTop.lean`,
`SpartanSromVerifier.lean` (`qBound`, `leafSize`), and the core contract at `85f0985`
(`Contract/{Relation,Signature,Oracle,Extractor,Certificate}.lean`,
`Library/{Words,WitnessSending,Fast}.lean`). Read-only; nothing rebuilt. The commands quoted below
were run on the committed files.

Method (the `adversarial-review` discipline applied to Rust/assembly): pass B first, forming the
expected bytes from the contract and the Lean `V` *before* reading the native `acc.rs`/`format.rs`;
then pass A (the stage's claims against the interfaces and the logs); then pass C (assembly,
reproducibility, hygiene). Severity: **major** = must fix before the stage is accepted; **minor** =
answer or fix; observations are marked as such.

## 0. Summary

No defect was found in the prover's code, in the bytes it writes, or in the native `acc` as a model
of the Lean `V`. Branch by branch the native `acc.rs`/`format.rs` make the same decisions as
`SpartanSromNode.V`, `clearLeaves`, `bundleOK`, `runBundle`, `WitnessSending.decode` and
`SigOk` (pass B, §1). The interface (handshake, inputs, outputs, exit codes, sandbox, caps) is
followed (pass A, §2). The assembly is within `x86-64-v2` outside the dispatched `field::hw::*`
functions, holds no forbidden directive or host path, and uses only classic GNU-as directives
(§3). The one **major** is evidential, not a code defect: the RESULT's table of checks against the
compiled Lean `acc` (§3.5) contains unfilled template placeholders, and the logs show that the only
bundle shapes the runner actually produces above level 1 (a bundle with a nested `N` slot: the
root, every stream node from link 2 on) were never checked by the Lean `acc` (F2-M1). The rest
are minors on provenance, units, phrasing and one robustness constant.

**Verdict: pass with one major to fix (F2-M1: complete or re-scope the Lean-agreement evidence)
and the minors answered.** The blocker outside this stage's control remains F1's/the badge's
superlinear file parse (RESULT §3.5, §7), which this review confirms from `logs/f2/lean-check/`
(88 s for a 539 KB file, 579 s for 1.08 MB, a 2.7 MB file killed at 701 s).

## 1. Pass B: byte agreement with the Lean `V` / `acc` (attack question 1)

Expected behaviour was derived from the contract and the Lean files first, then compared with the
native code. Items checked (file:line of the native side; the Lean counterpart in brackets):

| What | Native | Lean | Agree |
|---|---|---|---|
| `encode (.leaf s n)` = `enc64 0 ‖ s ‖ enc64 n`, 48 B | `format.rs:81-85` | `witWords`, `size_encode_leaf` | yes |
| `encode (.node …)` = `1 ‖ c₁ ‖ c₂ ‖ signedWords p₁ ‖ signedWords p₂`; strings length-prefixed, zero-padded to a word; digests 4 words; sig = idx ‖ 133 ots ‖ 16 path | `format.rs:48-95` | `Words.lean:157-169` | yes |
| strict decoder: tag ≠ 0/1 → none; a field past the end → none; padding bytes not checked; trailing words ignored | `format.rs:97-186` (`Rd`) | `Extractor.lean:416-467` (`readBytes` takes `⌈n/8⌉` words, `.take n`) | yes |
| `decode` word count = `|encode w|` (so `used == encode(w).len()`) | `format.rs:185` | `size_encode`, `readWit_witWords` | yes (by construction of both) |
| `V`: `|π| < 8` → false; tag 0 ∧ `|π| = 48` → `C`; tag 0 ∧ `|π| ≠ 48` → `L` (native: `> 48` → `L`, `8 ≤ |π| < 48` falls to `decode`, which yields a leaf → "wrong size" → reject; Lean's `leafProg` header check fails for `|π| < 80`) | `acc.rs:468-481` | `SpartanSromNode.lean:V` | yes |
| `C`: `n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n` | `acc.rs:470-477` | `clearLeafOK` | yes |
| `L`: `n ≤ chainCap`, `|π| = leafSize n`, `c = leafStmt h n`; `n = 0 → h = s`; else SNARK verifier on `π[80..]` | `verifier.rs:23-43` | `leafHeaderOK`, `leafProg` | yes |
| `N`: `encode w = π` exactly, `c = nodeStmt c₁ c₂`, `acc` on both children (recursive) | `acc.rs:482-492` | `V` (`_h : encodeF … = π`), `accWith` | yes |
| `B`: `encode W` a strict prefix; σ0 = slot 1's signature; every slot: empty trace, `σ = σ0`, `|π| ≤ proofCap`, `C` or canonical `N` with `c = nodeStmt`; leaves depth-first, child 1 first | `acc.rs:437-464, 493-500` | `clearLeaves`, `bundleProg` (`IsStrictPrefix`) | yes |
| `B` static: `SigOk vk (traceDigest []) σ0` once; `1 ≤ n_j ≤ chainCap`; `|T| = Σ(32 + leafSize n_j − 80)` exactly; `Σ qBound (kap n_j) ≤ 2^16` | `acc.rs:501-515` | `bundleOK` | yes (order of the no-query checks differs; no decision changes) |
| `B` run: per leaf in order, `c_j = leafStmt h_j n_j` then `snarkProg s_j n_j h_j π_S,j` with `h_j = T[o..o+32]`, `π_S,j = T[o+32..o+32+leafSize n_j−80]` | `acc.rs:516-526` | `runBundle` | yes |
| `qBound`: `1 + (2 + 2^μ) + (5(15+κ) + 9 + 2(8+κ)) + (1 + ⌈260/⌊256/ℓ_N⌋⌉ + 260(1+ℓ_N))` | `acc.rs:419-424`, `chain.rs:42-66` | `SpartanSromVerifier.lean:83-85`, `PCSBounds` (`muR`, `lk`, `lN`, `rows`, `tQ`), `SpartanProtocol` (`ly = 15+κ`, `lq = 8+κ`), `Transcript.nAns` | yes (also pinned by `q_bound_matches_v3`: 3533 at 16, 7774 at κ = 20) |
| `acc`: `|π| ≤ proofCap`, every `|q| ≤ queryCap`, `SigOk vk (traceDigest tr) σ`, `runSeq` exact (every entry used, each query equal) | `acc.rs:530-546`, `oracle.rs:416-448` (`Seq`) | `Submission.acc`, `OProg.runSeq` | yes (a mismatch sets `bad`; `v` continues with zero answers but `consumed()` then rejects; a native `Err` rejects before `consumed()` — both reject) |
| `traceDigest = BLAKE2s(0x54 ‖ (enc64 |q| ‖ q ‖ a)…)` | `format.rs:243-250` | `Signature.lean` | yes |
| `SigOk`: digits `(m[i] >> 2t) & 3`, checksum `Σ(3−d)` in 5 base-4 digits, chain `wotsStep j i s x = BLAKE2s(0x57 ‖ enc64 j ‖ i ‖ s ‖ x)` from `d` to 3, leaf `BLAKE2s(0x4B ‖ enc64 j ‖ ends)`, root by parity of `j` | `format.rs:254-300` | `Signature.lean` | yes |
| signed file: `u64 |π| ‖ π ‖ u64 m ‖ (u64 |q| ‖ q ‖ a)… ‖ u64 j ‖ 133×32 ‖ 16×32`, strict end | `format.rs:189-240` | `FORMAT.md`, `rfh/signed.py` | yes (idx `u32` on the wire → `u64` in the file, `service.rs:683`) |
| the prover's outputs: `L` = v3 bytes (`leaf_header` + `π_S`), `n = 0` → 80 B with `h = s`; `B` = `encode W ‖ T₁ ‖ T₂` with `W = node(c₁, c₂, (clear₁, [], σ0), (clear₂, [], σ0))`, `clear(L) = π[..48]`, `clear(B) = encode W_child`, `T(L) = π[48..]`, trace `tr₁ ‖ tr₂`; `N` when a child has `n = 0` or two `B` children disagree on σ0 | `make.rs:30-54, 100-177`, `main.rs:249-306` | BLUEPRINT §1.4, §7 | yes |

Nothing here is a finding. Two things the table makes explicit that the RESULT states only by
reading ("compared, by reading, with F1's `V`", §1): the equivalence of native `used == len` with
Lean's `encodeF w = π`, and that Lean's `IsStrictPrefix` also rejects the case `used > |π|`
(a node encoding missing its last bytes but decodable through zero padding), as the native code
does at `acc.rs:482`.

## 2. Pass A: the stage's claims against the interfaces and the logs

### 2.1 Completeness of outputs (question 2)

- `n = 0`: leaves are 80 B, nodes fall back to `N` (`make.rs:100-106, 157-165`); accepted by the
  native `acc` with canaries rejected (`logs/f2/selftest-asm-n0.log`). Correct per §1.3/§2.
- `n = chainCap = 2^20` and the season's `n = 2^18`: `parse_leaves`/`parse_leaf` accept them
  (`main.rs:135, 146`); proving would need far more than 11 GiB (15.1 GiB already at `2^16`,
  F2-m3) and `|π|` is above `proofCap`; the prover is OOM-killed or writes a rejected proof.
  Documented (RESULT §4, §6.2, §7). No silent success; see F2-m5 on the missing diagnostic.
- Large `r`: any power of two of starts (`main.rs:135`); levels built pairwise
  (`main.rs:270-303`); names `N<l>_<j>` and `root.bin` as PROVER.md §3; `r = 0` → `root.bin = L0`.
- Stream children: child 1 `L` or `B`, child 2 `L` (`make.rs:100-122, 157-166`); `σ0` from the `B`
  child or one `SIGN []` at the first merge (`main.rs:340-346`). Two `B` children with different
  σ0 → `N` (never produced by the runner).
- Crash surfaces: `verify_snark` asserts `ps.len() == snark_size()` (`verifier.rs:87`) but every
  caller has checked the length exactly (`verifier.rs:33`, `acc.rs:509`); `Cursor::take` cannot
  overrun for the same reason. `from_file` bounds `m` by the file length (`format.rs:220`) and
  `Rd::signed` bounds the trace count by the remaining words (`format.rs:153`), so a hostile
  `child1.bin` cannot make the node request allocate unboundedly. Panics abort (`panic=abort`),
  which the runner sees as a non-zero exit.

### 2.2 Trace correctness (question 3)

- The trace is the native verifier's query sequence replayed against the prover's answer table
  (`make.rs:42-53`, `oracle.rs:389-414`); a query not in the table is counted and never sent
  (`oracle.rs:407-409`), and fails the proof (`make.rs:49-51`). `SIGN` answers are compared entry
  by entry (`make.rs:60-62`). A 128-bit fingerprint collision (`oracle.rs:255-282`) can therefore
  only abort a request, never sign a wrong trace; the RESULT says this correctly.
- Query order: the native `verify_snark` asks the transcript's queries sequentially and the Merkle
  queries one at a time in `climb` order (`transcript.rs:97-111, 150-156`); `Replay` and `Seq`
  do not implement `ask_many`, so batching cannot reorder a replay or a check. The order equals the
  Lean `snarkProg`'s on the shapes the Lean `acc` was run on (`L0`, `N1_0`, `logs/f2/lean-check`),
  and the trace length equals `qBound (kap n)` exactly (3,533 at `n = 16`).
- σ0: one per tree and per stream (`main.rs:269-288`, `make.rs:159-162`); a `B` child's σ0 is
  reused, which is the same service lifetime in every runner flow (`bench.py:446-491`: one service
  per stream repeat). An `N` node needs its own `SIGN []` (its trace is empty but its signature is
  its own); the `n = 0` tree used 7 signatures for 7 files, as expected.

### 2.3 Interface robustness (question 4)

- Handshake (`main.rs:308-316`): circuit built, service connected, `VK` compared with `vk.hex`
  (present before start, PROVER.md §3), connections warmed, then `ready`; `go` awaited on stdin
  (`main.rs:197-210`); inputs read only after `go` (`main.rs:321, 333-336`); `proof.bin`
  written, then `done` (`main.rs:324-325, 349-350`). Matches `rfh/prover.py:166-224`. Nothing
  timed happens before `ready` except what PROVER.md allows (loading, untimed).
- `proof.bin` is written in place (`std::fs::write`), not by rename; the runner reads it only
  after `done`/exit and after killing the sandbox, so this is safe. Observation only.
- Exit codes: usage/input errors 2 (`main.rs:612-614`), any service refusal or I/O error 3 with the
  service's message (`service.rs:532-535, 647-654`), panics SIGABRT.
- Service caps: `QUERY` batches ≤ 4,096 items and about 4 MiB (`service.rs:527-529, 734`), a
  single query ≤ 2^20 checked (`service.rs:739`), body ≤ 2^24 checked (`service.rs:746`); `SIGN`
  count is `qBound`-bounded (≤ 2^16 by the static check) and its body stays under 16 MiB for every
  bundle that fits `proofCap`. Connections: pool of at most 60 (`service.rs:526`); see F2-m6.
- Long socket paths: the `/proc/self/fd/<dir>/<name>` route for paths ≥ 100 B
  (`service.rs:565-583`); the sandbox has `/proc` and the runner's path is short.
- Sandbox: no path outside `/work` is read except `RF_ORACLE`; nothing under `/setup`, `/usr` or a
  shell is needed. None of the syscalls `rfh/sandbox.py:33-43` denies is used by Rust std's
  threads, sockets, files or `available_parallelism`. Confirmed by the smoke run in the real
  sandbox (`logs/f2/harness-smoke.json`: `benchmark: pass`).
- Threads: `available_parallelism()` respects the affinity mask, so 16 under `taskset -c 0-15`.
  Memory: 9 MB at `n = 16`, 15.1 GiB at `n = 2^16` (above the 11 GiB cap, documented).

### 2.4 Measurements (question 6): spot checks

Five numbers of the RESULT re-derived from the logs:

1. §4 `n = 16` keyed: `prove` median of {0.1594, 0.1370, 0.1302, 0.1476, 0.1325} = 0.137 s,
   `replay` 0.044 s, total 0.185 s, RSS 9,192 kB (`logs/f2/bench-asm-n16.log`): as stated.
2. §4 `n = 16` service: `prove` 0.142 s, total 0.193 s, `SIGN` 0.004 s, oracle 0.014 s of which
   FS 0.0087 s: as stated.
3. §4 `n = 65536`: prove 47.110 s, replay 1.727 s, total 48.840 s, 525,034 Merkle queries of
   1.09 GB in 0.767 s keyed / 0.594 s service (`bench-asm-n65536.log`): as stated; RSS unit wrong
   (F2-m3).
4. §3.3 sizes: `L` at `n = 16` is 143,711 B with 3,533 entries and 248,875 query bytes; the trace
   in the file is `8 + 3533·40 + 248,875 = 390,203` and the file `8 + 143,711 + 390,203 + 8 +
   4,768 = 538,698` (`selftest-asm.log`): as stated. Each extra leaf adds 153,367 B to π
   (297,078 − 143,711): as stated.
5. §3.4 harness: `T_tree` 0.917 s, leaf requests 0.214–0.238 s, merges 0.019/0.026/0.042/0.055 s,
   `t_leaf` 0.280 = (Σ of 5 leaves 1.120)/4, `t_merge` 0.036, `S` 7.23, 64 DoS inputs rejected,
   69 + 18 canaries (`harness-smoke.json`): as stated, and the `M + 1` over `M` observation
   (§6.6) is confirmed in `bench.py:492`.

Also checked: §6.5 (`Popen.wait` polling) is plausible and the three identical 0.917 s readings
support it; `o_est` and `T_V` are reported, not claimed. Phrasing issues: F2-m4.

### 2.5 Gaming (question 7)

None found. No state survives a request (fresh process, nothing written outside `/work`); `setup`
writes nothing; nothing is keyed to the starts before `go`; the pre-`ready` work (circuit tables,
connections, one `VK` round trip) is input-independent and permitted by PROVER.md §3. The prover
reads `leaves.json`/`leaf.json`/`child*` and `vk.hex` only. Hashing goes through the service in
every mode the runner invokes (`Local` oracles are reachable only through development modes with
`--oracle`, `main.rs:183-193`).

## 3. Pass C: the assembly, the build, hygiene (question 5)

On the committed `prover.s` (8,699,228 B, SHA-256 `13544017…`, equal to the RESULT):

```
grep -c '\.incbin\|\.include' prover.s        → 0
grep -c '/home' prover.s; grep -c '/tmp\|/devops' prover.s   → 0, 0
grep -o '/rustc/[0-9a-f]*' | sort -u          → one hash (rustc b940084d…), 57 lines (std panic locations)
grep -c 'ymm'; grep -c 'zmm'                   → 0, 0
grep -cE '\bv(mov|p|add|…)[a-z0-9]*\b'         → 0   (no VEX-encoded instruction)
grep -nE '\b(lzcnt|tzcnt|andn|bextr|bls.|bzhi|pdep|pext|sh[lr]x|sarx|rorx|mulx|movbe|adcx|adox|crc32|aesenc|sha256…)' → none
popcntq: 16 lines, all in std's Once::call_once_force (par::threads), x86-64-v2
pextrq/pinsrd: SSE4.1, x86-64-v2
xgetbv: 1, in std_detect (guarded by CPUID.OSXSAVE)
pclmulqdq: 13, all inside field::hw::{clmul,mul_k,mul_ek,mul_e} (#[target_feature]); the
  `#[inline]` on hw::cl cannot cross into a caller without the feature
```

Directives used: `.cfi_*`, `.p2align`, `.section` (`.text.unlikely.*`, `.rodata.cst{4,8,16,32}`,
`.rodata.str1.1`, …), `.type`, `.size`, `.long/.quad/.byte/.short/.zero/.ascii/.asciz/.uleb128`,
`.weak`, `.globl`, `.ident`, one `.file "spartan_srom_prover.<hash>-cgu.0"`, `.att_syntax`. No
`.prefalign`, `.addrsig`, `.file N "dir" "file"`, `.loc`, `{evex}`/`{vex}` prefixes or other
directive younger than binutils 2.30; by reading, Ubuntu 24.04's `as` 2.42 assembles it (not run
here: only 2.46 is installed). Instructions outside the dispatched functions are all within
`x86-64-v2`; the runners (EPYC, Xeon, AVX2 and PCLMULQDQ present) will take the `hw` path, which
was validated only under qemu TCG (`-cpu Haswell`, `max`: products equal on 50,000 inputs; proofs
at `n = 1, 16, 64` equal v3's, `logs/f2/qemu-asm.log`) — see F2-m7.

Build: `build-asm.sh` is deterministic across two target directories and a copied crate
(`logs/f2/determinism.log`, same `prover.s` and binary SHA-256); the sandboxed harness build gives
the same binary (`harness-smoke.json` `binary_sha256`). Paths are remapped; the only external input
is the toolchain version, which is not pinned by a file (F2-m2).

Hygiene: module headers say what each file is for; the native `acc` names the Lean definition it
mirrors; `#![allow(dead_code)]` is crate-wide (`main.rs:35`) for KAT helpers (acceptable, noted).
`Cargo.toml` says `codegen-units = 4` while the submitted build uses 1 through `--config`; the
tests therefore test a differently compiled binary (F2-m7).

## 4. Findings

### Major

**F2-M1 — The Lean-`acc` evidence in the RESULT is unfinished and narrower than its headline.**
*Claim attacked:* RESULT status (line 8): "F1's compiled `acc` accepts this prover's
service-signed leaf and bundle proofs and rejects their canaries"; BLUEPRINT §7: "Output proofs
must be accepted by the compiled `acc`". *Evidence:* RESULT §3.5 lines 251–253 are the literal
placeholders `| ROOT_RESULT |`, `| STREAM_RESULT |`, `| CANARY_RESULT |`. In `logs/f2/lean-check/`,
`root.out` and `snode2.out` are empty, `snode4.out` reads `Command terminated by signal 15` after
700.98 s, and `run.log`/`run2.log` record exactly three completed checks: `L0.bin` accept, `N1_0.bin`
accept, two `L0` canaries reject. `N1_0` is a bundle of two `C` slots. Every bundle the runner
produces above level 1 (the tree root at `r ≥ 2`, every stream node from link 2 on) has a nested
`N` slot (`clear(B) = encode W_child`, `make.rs:109-119`) and exercises the recursive arm of the Lean
`clearLeaves` (`SpartanSromNode.lean`, the `decodeF p.π` / `encodeF … = p.π` / `nodeStmtF` branch)
against native bytes; that arm has never been run on this prover's output. The reading-based
comparison in §1 of this review finds the two agree, but the stage's claim is empirical and the
table that should carry it is template text. *Fix:* run `srom-run verify` (or the finished F1 badge
`verify`) to completion on one nested bundle — `root.bin` of the `r = 2, n = 16` tree
(2,169,384 B) or, to shorten the superlinear parse, the root of an `r = 2, n = 1` tree (about
1.4 MB, comparable to `N1_0`'s 579 s) — plus one stream node with a nested slot and its canaries;
replace the three placeholders with the results (or with "not run: killed at 701 s" and a stated
gap, and narrow the status line to what was checked). *Cost:* no code; one to three runs of
10–60 min each, with `timeout`, on a free core.

### Minor

**F2-m1 — The stream-links table was measured with an earlier binary.** RESULT §3 header: "all
with the linked assembly binary `F/prover-asm`, SHA-256 `30b46975…`"; §3.3 cites
`F/links-n{16,1024,4096}.log`. Those logs name `prover-asm (sha256 0b75b92ec5e260fe)`, a build
from 19:24, before the final build (19:26–19:29). The sizes and verdicts agree with the final
binary's runs, so the table is very likely still right, but the provenance claim is false as
written. *Fix:* re-run `selftest.py stream` for the three `n_f` with the final binary (about 1 min)
or add the qualification. *Cost:* minutes.

**F2-m2 — No toolchain pin file.** README and RESULT state rustc 1.99.0 / LLVM 23.1.1, but
`prover/` has no `rust-toolchain.toml`; the byte-for-byte rebuild of `prover.s` depends on the
reader installing that exact version by hand. *Fix:* add `prover/rust-toolchain.toml` with
`channel = "1.99.0"` and `profile = "minimal"` (cargo then refuses, rather than silently emitting a
different `.s`, on another toolchain). *Cost:* two lines; a note in README.

**F2-m3 — Peak-RSS unit.** `/usr/bin/time -v` reports KiB: 15,788,764 kB at `n = 65536` is
15.06 GiB = 16.17 GB, not "15.79 GB" / "15.8 GB" (RESULT §4 table, §4 findings, §6.2, §7). The
conclusion (above the 11 GiB cap) stands; the number should read 15.1 GiB (16.2 GB). The same
applies to the 9.2 MB / 265 MB / 1.02 GB / 3.97 GB entries (KiB-based). *Cost:* text.

**F2-m4 — "Going through the service costs no measurable prover time at any `n`" overstates.**
At `n = 16` the oracle's own counters do measure it: FS round trips 0.0003 → 0.0087 s, oracle
share 4.7 % → 10 %, `prove` 0.137 → 0.142 s (+4 %); above `n = 1024` the difference is within the
VM's noise (±5 %). *Fix:* "within the run-to-run noise of this VM (≤ 4 % at `n = 16`, where the
153 sequential round trips add about 8 ms; < 1 % above)". *Cost:* text.

**F2-m5 — Outputs above a cap are written without a diagnostic.** The prover never checks
`proofCap` on what it writes (`main.rs:261, 290, 323, 348`), so a bundle of 1,063,913 B is written
and `done` printed; the runner's only signal is `acc`'s rejection, and its `stderr[-300:]` is empty.
A one-line `eprintln!` when `|π| > PROOF_CAP` (and when a `SIGN` body would exceed 2^24) would make
the harness's failure message self-explaining at no cost; exiting non-zero would change nothing
for the score. *Cost:* three lines in `main.rs`.

**F2-m6 — Connection pool size.** `MAX_CONNS = 60` against the service's cap of 64, and
`warm(par::threads())` opens up to 60 before `ready` (`main.rs:312`, `service.rs:597-605`). On a
runner with ≥ 60 CPUs the next stream request's warm-up can race the previous sandbox's closing
sockets; a `CAP` response is fatal (exit 3) and ends the stream. Beyond about 16 connections there
is no gain (the service computes on the same CPUs; 1.8 GB/s was reached with 16). *Fix:*
`MAX_CONNS = 32` and `warm(threads.min(16))`, or document the assumption that runners have fewer
than 60 CPUs. *Cost:* one constant.

**F2-m7 — The hardware `pclmulqdq` path and the tested binary.** (a) The runners have
`pclmulqdq`, this VM has not; the `hw` path was validated under qemu TCG only (correct products on
50,000 inputs and v3-equal proofs at `n = 1, 16, 64`). (b) `cargo test` compiles with
`codegen-units = 4` and no LTO, a different binary from the submitted one (the 27 unit tests are
not evidence about `prover.s`; the selftests and KATs with the linked binary are). *Fix:* say so
in the RESULT; if a machine with `pclmulqdq` is available before the season, run `selftest-field`
and the `keyed-kat` there once. *Cost:* a sentence; optionally one run elsewhere.

**F2-m8 — The RESULT does not name the harness it ran against.** The worktree's `.contract`
submodule is empty; the smoke used `recursion.fast-v4h` at harness commit
`bb724bb06ec94ec54db382fd4c203d87e6c80863` (`harness-smoke.json`), service `d6003237…`. The
RESULT quotes the service hash but not the harness commit. *Fix:* add the commit to §3.4. *Cost:*
text.

### Observations (no action required)

- `fp` collisions (`oracle.rs:255`): the abort is a liveness failure of that one request, with
  probability about `N²/2^128` for `N ≤ 5·10^5` queries; acceptable, and the RESULT's statement is
  correct.
- `N` fallback with child 2 at `n = 0` and a non-trivial child 1 carries child 1's whole signed
  proof (π and trace) inside π, so it is above `proofCap` at once; only `n_f = 0` reaches it.
- `proof.bin` is not written by rename; safe under the runner's protocol (read after `done`).
- `popcnt` and `xgetbv` appear in `prover.s` (std); both are within `x86-64-v2` or guarded, and
  worth a word in RESULT §2's "Content" row for completeness.
- The three `clmul`-free KATs against F1's Lean `P` (`n = 1, 16`) and against v3 (`n = 1, 2, 16,
  64`) are the right ones; the Lean `acc` evidence for `L` covers `n = 16` only (RESULT §3.5),
  which is as much as the parse time allows today.

## 5. Verdict

**Pass, conditional on F2-M1.** The prover implements BLUEPRINT §1, §2 and §7 faithfully; the
native `acc` is a correct model of the Lean `V` on every branch and static check examined; the
interface, the sandbox and the caps are respected; the assembly is portable to the stated runners
and reproducible on the stated toolchain; the measurements quoted are supported by the logs (five
of five spot checks) with the unit and provenance corrections of F2-m1 and F2-m3. The major is
about evidence the RESULT promises and does not yet contain: a compiled-Lean acceptance of a bundle
with a nested `N` slot (the shape of every root and every stream node after link 1), and the
removal of the three template placeholders in §3.5. The entry's own blocker — the badge's
superlinear parse (88 s for the smallest leaf against `verify_s = 60`) — is correctly reported by
F2 and is owed by F1/the harness, not by this stage.
