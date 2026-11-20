#!/usr/bin/env python3
"""A local end-to-end run of the bot (untrusted by nothing: a test tool). A temporary bare git
repository stands for GitHub's (with `main`, `refs/pull/N/head` and the bot's `data` branch and
tags), `FakeGitHub` for the REST API, and fixture result.json files for the core's evaluation.

  python3 -I .github/bot/simulate.py         runs the scenario and prints what the bot did

The tests (`tests/test_e2e.py`) drive the same pieces."""
import json
import os
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import flows  # noqa: E402
import rfqueue  # noqa: E402

REPO = "scaraven/recursion.fast-submissions"
PIN = "c0dec0dec0dec0dec0dec0dec0dec0dec0dec0de"   # fictional
GENV = {"GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
        "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t", "GIT_AUTHOR_DATE": "2026-11-03T00:00:00Z",
        "GIT_COMMITTER_DATE": "2026-11-03T00:00:00Z"}


def git(d, *args, input=None):
    env = dict(os.environ, **GENV)
    r = subprocess.run(["git", "-C", d, *args], input=input, capture_output=True, env=env)
    if r.returncode:
        raise RuntimeError(f"git {' '.join(args)}: {r.stderr.decode()}")
    return r.stdout.decode().strip()


def commit_tree(bare, parent, files, message, modes=None):
    """A commit on `parent` with `files` ({path: bytes | None}) changed; `modes` overrides a path's
    mode (120000, 160000) with its content as the target."""
    idx = os.path.join(bare, "sim-index")
    if os.path.exists(idx):
        os.remove(idx)
    env = dict(os.environ, **GENV, GIT_INDEX_FILE=idx)
    run = lambda *a, input=None: subprocess.run(["git", "-C", bare, *a], input=input, capture_output=True,  # noqa: E731
                                                env=env, check=True).stdout.decode().strip()
    if parent:
        run("read-tree", parent)
    for path, data in files.items():
        mode = (modes or {}).get(path, "100644")
        if data is None:
            run("update-index", "-z", "--index-info", input=b"0 " + b"0" * 40 + b"\t" + path.encode() + b"\0")
        elif mode == "160000":
            run("update-index", "--add", "--cacheinfo", f"160000,{data.decode()},{path}")
        else:
            oid = run("hash-object", "-w", "--stdin", input=data)
            run("update-index", "--add", "--cacheinfo", f"{mode},{oid},{path}")
    tree = run("write-tree")
    return run("commit-tree", tree, "-m", message, *(["-p", parent] if parent else []))


def good_root(name, salt="", notes=None):
    p = f"submissions/{name}/"
    return {p + "claim.json": b'{"error": "1/2", "completeness_error": "0", "qV": 1, "fuel_base": 0, "fuel_per_word": 8}',
            p + "lean/Solution.lean": f"-- solution {salt}\n".encode(),
            p + "prover/prover.s": f"# prover {salt}\n".encode(),
            p + "NOTES.md": (notes if notes is not None else f"# {name}\n\nAgent: Opus 5.5\nBuilds on: #1, #2\n\nidea {salt}\n").encode(),
            p + "README.md": f"# {name}\n".encode()}


class FakeGitHub:
    """The REST calls the bot makes, against the bare repository."""

    def __init__(self, bare, clock=None):
        self.bare, self.prs, self.perms, self.clock = bare, {}, {}, clock
        self.comments, self.status_log, self.dispatches, self.by_sha = [], [], [], {}

    def main(self):
        return git(self.bare, "rev-parse", "refs/heads/main")

    def open_pr(self, n, author, files, title="entry", draft=False, labels=(), modes=None, base="main", head_owner=None):
        sha = commit_tree(self.bare, self.main(), files, f"PR {n}", modes)
        git(self.bare, "update-ref", f"refs/pull/{n}/head", sha)
        self.prs[n] = {"number": n, "state": "open", "draft": draft, "title": title, "user": {"login": author},
                       "head": {"sha": sha, "repo": {"owner": {"login": head_owner or author}}}, "base": {"ref": base},
                       "labels": [{"name": x} for x in labels],
                       "created_at": "2026-11-03T00:00:00Z", "_base_sha": self.main()}
        return sha

    def push(self, n, files, modes=None):
        p = self.prs[n]
        sha = commit_tree(self.bare, p["head"]["sha"], files, f"PR {n} push", modes)
        git(self.bare, "update-ref", f"refs/pull/{n}/head", sha)
        p["head"]["sha"] = sha
        return sha

    def pr(self, n):
        p = dict(self.prs[n])
        p["changed_files"] = len(self.pr_files(n) or [])
        return json.loads(json.dumps(p))

    def pr_files(self, n, limit=3000):
        p = self.prs[n]
        out = git(self.bare, "diff", "--name-status", "-M", p["_base_sha"], p["head"]["sha"])
        files = []
        for line in out.splitlines():
            parts = line.split("\t")
            if parts[0].startswith("R"):
                files.append({"filename": parts[2], "previous_filename": parts[1], "status": "renamed"})
            else:
                files.append({"filename": parts[1], "status": parts[0]})
        return None if len(files) > limit else files

    def permission(self, login):
        return self.perms.get(login, "read")

    def comment(self, n, body):
        self.comments.append((n, body))

    def issue(self, title, body):
        self.issues = getattr(self, "issues", []) + [(title, body)]

    def set_status(self, sha, state, description, target_url=None, creator="github-actions[bot]"):
        self.status_log.append((sha, state, description))
        t = flows.now_iso(self.clock) if self.clock else "2026-11-03T00:00:00Z"
        self.by_sha.setdefault(sha, []).insert(0, {"state": state, "description": description, "created_at": t,
                                                   "context": "recursion.fast/evaluation", "creator": {"login": creator}})

    def statuses(self, sha):
        return list(self.by_sha.get(sha, []))

    def open_prs(self):
        return [{k: v for k, v in self.pr(n).items() if k != "changed_files"} for n, p in sorted(self.prs.items())
                if p["state"] == "open"]

    def dispatch(self, workflow, ref, inputs=None):
        self.dispatches.append((workflow, ref))

    def caches(self, prefix):
        return [{"key": k} for k in getattr(self, "cache_keys", []) if k.startswith(prefix)]

    def delete_cache(self, key):
        self.cache_keys.remove(key)


def make_result(run_id, verdict="ACCEPT", S=1.0, comparable=True, harness=PIN, prover="a" * 64, machine_ok=True,
                organiser_error=None, stream=True, every=True, legacy=False, reject_stage=None):
    """A result as the core's aggregate.py writes it (the fields the bot reads). `comparable=False`:
    a truncated stream; `machine_ok=False`: another machine's fingerprint, the organiser's ERROR;
    `stream=False`: no stream recorded (a REJECT at the certificate, so no benchmark part, or inside
    the stream). `S` is the score of `final` (P_total · |π_16|, |π_16| in bytes, so in seconds ·
    bytes); `S_every`, the score of `every`, prices the largest proof (an intermediate one 80,000
    bytes larger than the final one), so it is `S` times a fixed factor, 360000 / 280000, and the
    two tracks rank alike; `every=False`: eligible for
    `final` only (an intermediate output not accepted), with the core's `tracks_reason`; `legacy`: a
    score without `tracks` (an earlier season's core), the sum alone; `reject_stage`: a REJECT's
    stage, the core's top-level field (absent by default; with a stream, the stream's `leaf_data`
    marks the result as this rules' core's, so a REJECT without a stage is final)."""
    fp = "f" * 64
    if not machine_ok:
        verdict, comparable = "ERROR", False
    r = {"schema": "recursion.fast/v6/result-1", "verdict": verdict, "comparable": comparable,
         "truncated": not comparable and machine_ok, "harness_commit": harness, "job": f"{REPO}/actions/runs/{run_id}/attempts/1",
         "machine": {"fingerprint": fp if machine_ok else "e" * 64, "expected": fp, "matches": machine_ok and stream},
         "stream": {"shape": {"M": 16, "n": 1 << 18}, "leaf_data": {"xof": "shake256", "domain": "recursion.fast/leaf-data/v1"},
                    "truncated": not comparable and machine_ok} if stream else None,
         "runner": {"name": "rf-bench-1", "environment": "self-hosted", "labels": ["rf-bench"]},
         "reasons": ([] if verdict == "ACCEPT" else ["the entry failed: `boom` @someone"] if machine_ok else
                     [f"organiser ERROR: the machine fingerprint is mismatched (fingerprint {'e' * 64}, the season expects {fp})"]),
         "prover_sha256": prover}
    if not machine_ok or organiser_error:
        r["organiser_error"] = organiser_error or "fingerprint"
    if reject_stage is not None:
        r["reject_stage"] = reject_stage
    if verdict in ("ACCEPT", "PROVISIONAL"):
        pi, pi_max = 280000, 360000
        f, fe = pi, pi_max
        P = S / f
        if legacy:
            r["score"] = {"S": S, "P_bar": S * 0.8, "V_bar": S * 0.2, "M": 96, "c_P": 1.0}
        else:
            r["score"] = {"S": S, "P_total_s": P, "size_factor": f, "final_pi_bytes": pi,
                          "pass_totals_s": [P * 1.004, P, P * 0.998], "median_pass": 2,
                          "M": 16, "sum_n": 16 << 18, "c_P": 1.0,
                          "tracks": {"final": "S", "every": "S_every"} if every else {"final": "S"}}
            if every:
                r["score"].update(S_every=P * fe, size_factor_every=fe, max_pi_bytes=pi_max)
            else:
                r["score"]["tracks_reason"] = {"every": "output 3 rejected by acc"}
    return r


def fake_verify(pin):
    def verify(path, result, min_attempt=1):
        ok = result.get("harness_commit") == pin and "/actions/runs/" in str(result.get("job"))
        return {"attested": ok, "record_ok": ok and result.get("verdict") == "ACCEPT" and result.get("comparable") is True,
                "reason": "" if ok else "fake: not attested"}
    return verify


class World:
    """A bare 'GitHub' repository with a `main`, a fake API, and a clock."""

    def __init__(self, root=None):
        self.dir = root or tempfile.mkdtemp(prefix="rf-sim-")
        self.bare = os.path.join(self.dir, "github.git")
        os.makedirs(self.bare)
        git(self.bare, "init", "-q", "--bare")
        for k, v in (("gc.auto", "0"), ("receive.autogc", "false"), ("maintenance.auto", "false")):
            git(self.bare, "config", k, v)      # no background gc racing the bot's fetches and pushes
        main = commit_tree(self.bare, None, {"README.md": b"# recursion.fast submissions\n",
                                             "records.json": b'{"version": 1, "records": {}}\n',
                                             "submissions/README.md": b"roots\n", ".contract": PIN.encode(),
                                             "submissions/example/NOTES.md": b"kept\n"},
                           "main", modes={".contract": "160000"})
        git(self.bare, "update-ref", "refs/heads/main", main)
        self.gh = FakeGitHub(self.bare, self.clock)
        self.t, self.run, self.pin = 0, 100, PIN
        self.logs = []

    def clock(self):
        import datetime
        self.t += 1
        return datetime.datetime(2026, 11, 3, tzinfo=datetime.timezone.utc) + datetime.timedelta(seconds=self.t)

    def ctx(self, run_id=None):
        return flows.Ctx(self.gh, REPO, self.bare, self.pin, run_id=run_id or self.run, clock=self.clock,
                         sleep=lambda s: None, verify=fake_verify(self.pin), log=self.logs.append)

    def state(self):
        raw = subprocess.run(["git", "-C", self.bare, "show", "data:submissions.json"], capture_output=True).stdout
        return rfqueue.load(raw or None, REPO, self.pin)

    def show(self, ref_path):
        r = subprocess.run(["git", "-C", self.bare, "show", ref_path], capture_output=True)
        return r.stdout if r.returncode == 0 else None

    def intake(self, n, sync=True):
        """The intake of #n, then the sync it dispatches."""
        k = flows.intake(self.ctx(), n)
        if sync:
            flows.sync(self.ctx())
        return k

    def evaluate(self, result=None, force=None, retire=None, resume=False, track=None, confirm=True, again=None):
        """select → (the core's evaluation, replaced by `result(entry, run_id)`) → publish.
        `retire`, `track`: the owner retires that record in that track first. A record candidate
        (decide.py) is queued for its confirmation run: with `confirm`, that run follows at once,
        with the result `again` (default: `result` once more), and the confirmation's published
        entry is returned with the first run's selected entry; without it, the candidate is left
        queued."""
        self.run += 1
        ctx = self.ctx(self.run)
        e = flows.select(ctx, force, retire, resume, track)
        if e is None:
            return None, None
        path = None
        if result is not None:
            r = result(e, self.run)
            if r is not None:
                path = os.path.join(self.dir, f"result-{self.run}.json")
                with open(path, "w") as f:
                    json.dump(r, f)
        p = flows.publish(ctx, e["id"], path)
        if confirm and p and p["status"] == "queued" and (p.get("confirm") or {}).get("run_url") == p.get("run_url"):
            _e2, p = self.evaluate(again or result, confirm=False)
        return e, p

    def cleanup(self):
        shutil.rmtree(self.dir, ignore_errors=True)


def main():
    w = World()
    try:
        g = w.gh
        g.open_pr(1, "alice", good_root("alpha", "1"))
        g.open_pr(2, "bob", good_root("beta", "2"))
        g.open_pr(3, "mallory", {**good_root("gamma", "3"), ".github/workflows/x.yml": b"evil"})
        for n in (1, 2, 3):
            print(f"intake #{n}:", w.intake(n, sync=False))
        print("sync: changed", flows.sync(w.ctx()))
        e, p = w.evaluate(lambda e, run: make_result(run, S=10.0))
        print("evaluated", e["id"], "->", p["status"], "(no record stood at the pin)")
        # the record rule needs S < (1 - MARGIN) * S_record (MARGIN = 0.02): 9.9 is within the margin
        # of 10, 9.0 beats it
        e, p = w.evaluate(lambda e, run: make_result(run, S=9.9, prover="b" * 64))
        print("evaluated", e["id"], "->", p["status"], "|", p["reasons"][-1])
        g.open_pr(6, "erin", good_root("zeta", "6"))
        w.intake(6)
        e, p = w.evaluate(lambda e, run: make_result(run, S=9.0, prover="e" * 64))
        print("evaluated", e["id"], "->", p["status"], "|", p["reasons"][-1])
        rec = json.loads(w.show("main:records.json"))["record"]
        print("main records.json:", {t: r and r["id"] for t, r in rec.items()},
              "main roots:", git(w.bare, "ls-tree", "--name-only", "main", "submissions/").split())
        # a run off the season's machine is the organiser's ERROR, re-queued in its place; a truncated
        # stream is the entry's `unranked`
        g.open_pr(7, "frank", good_root("eta", "7"))
        w.intake(7)
        e, p = w.evaluate(lambda e, run: make_result(run, S=1.0, prover="f" * 64, machine_ok=False))
        print("another machine:", e["id"], "->", p["status"], "|", p["reasons"][-2])
        e, p = w.evaluate(lambda e, run: make_result(run, S=1.0, comparable=False, prover="f" * 64))
        print("re-run, truncated:", e["id"], "->", p["status"], "|", p["reasons"][-1])
        # no cap per author: with nobody else waiting, one author's entries run back to back; another
        # author's entry then goes before that author's next (the fair order)
        for n in (8, 9, 10, 12):
            g.open_pr(n, "carol", good_root(f"c{n}", str(n)))
            w.intake(n)
        for _ in range(3):
            e, p = w.evaluate(lambda e, run: make_result(run, "REJECT"))
            print("carol:", e["id"], "->", p["status"])
        g.open_pr(11, "dave", good_root("theta", "11"))
        w.intake(11)
        e, p = w.evaluate(lambda e, run: make_result(run, "REJECT"))
        print("fair order: dave's #11 before carol's #12:", e["id"], "->", p["status"])
        e, p = w.evaluate(lambda e, run: make_result(run, "REJECT"))
        print("then carol's #12:", e["id"], "->", p["status"])
        # the two tracks: an entry whose intermediate outputs are not all accepted is scored in
        # `final` only, and takes the final record only (the every record stands)
        g.open_pr(13, "grace", good_root("iota", "13"))
        w.intake(13)
        e, p = w.evaluate(lambda e, run: make_result(run, S=8.0, every=False, prover="1" * 64))
        print("tracks: final only:", e["id"], "->", p["status"], p["record_in"], "|", p["reasons"][-2], "|", p["reasons"][-1])
        rec = json.loads(w.show("main:records.json"))["record"]
        print("records.json:", {t: r and r["id"] for t, r in rec.items()},
              "main roots:", git(w.bare, "ls-tree", "--name-only", "main", "submissions/").split())
        # the confirmation (decide.py): a lucky first run that beats the final record is a candidate;
        # its confirmation run (the same commit, next, at the pin) does not beat it, so no record
        g.open_pr(15, "ivan", good_root("lucky", "15"))
        w.intake(15)
        e, p = w.evaluate(lambda e, run: make_result(run, S=7.6, every=False, prover="6" * 64), confirm=False)
        print("confirmation: candidate:", e["id"], "->", p["status"], "| took", p["confirm"]["took"], "|", p["reasons"][-1][:60])
        e, p = w.evaluate(lambda e, run: make_result(run, S=7.95, every=False, prover="6" * 64))
        print("confirmation: second run:", e["id"], "->", p["status"], p["record_in"], "|", p["reasons"][-1][:110])
        # and one whose confirmation also beats it: the record, with the worse of the two scores
        g.open_pr(16, "ivan", good_root("steady", "16"))
        w.intake(16)
        e, p = w.evaluate(lambda e, run: make_result(run, S=7.5, every=False, prover="7" * 64),
                          again=lambda e, run: make_result(run, S=7.7, every=False, prover="7" * 64))
        print("confirmation: confirmed:", e["id"], "->", p["status"], p["record_in"], "S =", p["score"]["S"])
        # the pin moves within the season: each track's record is ported first and keeps its crown
        # (two ports here, the final's and the every's, each a candidate only in its own track)
        g.open_pr(5, "dave", good_root("eps", "5"))
        w.intake(5)
        w.pin = "c" * 40
        provers = {6: "e" * 64, 16: "7" * 64}           # a port runs its record's own prover binary
        for _ in range(2):                              # (a port is never confirmed: the organiser's)
            e, p = w.evaluate(lambda e, run: make_result(run, S=7.7 if e["pr"] == 16 else 9.0, every=e["pr"] != 16,
                                                         harness=w.pin, prover=provers[e["pr"]]))
            print("pin moved; a record is ported first:", e["id"], "->", p["status"], p["record_in"], "| port of", e.get("port_tracks"))
        # an entry that beats both records takes both
        e, p = w.evaluate(lambda e, run: make_result(run, S=7.0, harness=w.pin, prover="5" * 64))
        print("then at the new pin:", e["id"], "->", p["status"], p["record_in"], "|", "; ".join(p["reasons"][-2:]))
        # the owner retires it in the every track only: it still holds the final record
        g.open_pr(14, "heidi", good_root("kappa", "14"))
        w.intake(14)
        e, p = w.evaluate(lambda e, run: make_result(run, S=7.5, harness=w.pin, prover="4" * 64),
                          retire=p["id"], track="every")
        print("retired in every only:", e["id"], "->", p["status"], p["record_in"], "|", "; ".join(p["reasons"][-2:]))
        rec = json.loads(w.show("main:records.json"))
        print("records.json:", rec["core"][:8], {t: r and r["id"] for t, r in rec["record"].items()},
              "history:", {t: [h["id"] + ":" + h["status"] for h in hs] for t, hs in rec["history"].items()})
        print("main roots:", git(w.bare, "ls-tree", "--name-only", "main", "submissions/").split())
        # copies: another author's root with an earlier entry's prover/ (new NOTES, a new root name) is
        # invalid, and so is a PR opened from another user's branch
        g.open_pr(17, "mallory", good_root("mine", "16", notes="# mine\n\nAgent: x\n"))
        print("a copied prover/:", w.intake(17), "|", w.state()["submissions"][-1]["reasons"][0])
        g.open_pr(18, "mallory", good_root("theirs", "18"), head_owner="heidi")
        print("another user's branch:", w.intake(18), "|", w.state()["submissions"][-1]["reasons"][0][:90])
        print("comments:", len(g.comments), "statuses:", len(g.status_log), "dispatches:", len(g.dispatches))
        print("queue:", [(x["id"], x["status"]) for x in w.state()["submissions"]])
    finally:
        w.cleanup()


if __name__ == "__main__":
    sys.exit(main())
