"""The bot's steps (TRUSTED): intake, sync, select, publish, and the sync of `main` to the records.
Each reads GitHub through `ctx.gh` and git through `gitdata.Repo(ctx.git_url)`, so the tests and
`simulate.py` drive them against a local bare repository and a fake API.

Writers of `data` (two, so that racing intakes cannot lose entries): `sync` (workflow sync.yml, concurrency `rf-data`) is the only writer
of new queue entries; `select` and `publish` (evaluate-next.yml, `rf-eval`) mark entries running and
evaluated. The intake writes nothing on `data`: it prechecks, creates the retention tag, and sets
the commit status `recursion.fast/evaluation` to pending "queued", whose `created_at` is the queue
timestamp (only the base repository's token can set it); then it dispatches `sync`, which rescans
every open pull request and is idempotent, so coalesced runs lose nothing.

No step runs entry code or checks an entry out: a pull request is read as git objects and API
JSON. Every write to `data` and `main` is an optimistic transaction (`gitdata.Repo.transact`), and a
`data` that cannot be read aborts the step (nothing is reset)."""
import copy
import json
import time

import precheck
import render
import rfqueue
import wfcheck
from common import ID_RE, LOGIN_RE, PAUSING_ERRORS, MAX_TEXT_BYTES, ROOT_RE, SHA_RE, STATUS_CONTEXT, clean, entry_id, now_iso
from decide import (badge_sha, build_manifest_sha, cache_check, cache_check_stands, cache_retry, candidate, confirmed, decide,
                    result_prover_keys)
from gitdata import Changes, Repo

DATA, NOTES_MD = "data", "notes.md"
ORGANISER = ("admin", "maintain", "write")
BOT_LOGIN = "github-actions[bot]"
# descriptions of the bot's statuses after which a head may be admitted again
READMIT = ("withdrawn", "superseded", "intake failed")
# the time one sync spends examining heads (sync.yml's job has 30 minutes): past it, the sync writes
# what it has examined and dispatches the next sync, which goes on where it stopped (every head it
# recorded is skipped), so no number of slow heads can keep `data` from being written
SYNC_BUDGET_S = 15 * 60


class Ctx:
    """Everything a step needs from its environment."""

    def __init__(self, gh, repo, git_url, pin, token=None, run_id="0", run_attempt=1, server="https://github.com",
                 default_branch="main", clock=None, sleep=time.sleep, verify=None, log=print, bot_login=BOT_LOGIN,
                 monotonic=time.monotonic):
        self.gh, self.repo, self.git_url, self.pin, self.token = gh, repo, git_url, pin, token
        self.monotonic = monotonic
        self.run_id, self.run_attempt, self.server, self.default_branch = str(run_id), int(run_attempt), server, default_branch
        self.run_url = f"{server}/{repo}/actions/runs/{self.run_id}"
        self.clock, self.sleep, self.verify, self.log, self.bot_login = clock, sleep, verify, log, bot_login

    def git(self):
        return Repo(self.git_url, self.token)

    def now(self):
        return now_iso(self.clock)


def _state(ctx, snap):
    return rfqueue.load(snap.read("submissions.json"), ctx.repo, ctx.pin)


def _write_state(ctx, ch, snap, st, extra_reads=None):
    """Puts submissions.json and the regenerated notes.md into `ch`."""
    extra = extra_reads or {}
    ch.put("submissions.json", rfqueue.dump(st, ctx.clock))
    ch.put(NOTES_MD, render.notes_md(st, lambda p: extra[p] if p in extra else snap.read(p, MAX_TEXT_BYTES), ctx.repo))


def _labels(pr):
    return {(lab.get("name") or "").lower() for lab in pr.get("labels") or []}


def _try(ctx, what, fn, *a):
    """One side effect (a status, a comment, a dispatch): logged, never stopping the others.
    Returns False on failure."""
    try:
        fn(*a)
        return True
    except Exception as ex:  # noqa: BLE001
        ctx.log(f"{what} failed: {ex.__class__.__name__}: {str(ex)[:200]}")
        return False


def bot_statuses(ctx, sha):
    """The bot's statuses of the context on `sha`, newest first."""
    return [s for s in ctx.gh.statuses(sha) if s.get("context") == STATUS_CONTEXT
            and (s.get("creator") or {}).get("login") == ctx.bot_login]


def main_roots(git, branch="main"):
    """The directory names under `submissions/` on `main`."""
    head = git.fetch(f"refs/heads/{branch}", local="refs/rf/main-roots")
    if not head:
        return set()
    return {p.split("/", 1)[1] for mode, typ, _s, p in git.ls_tree(head, "submissions")
            if typ == "tree" and p.count("/") == 1}


# ---- examine: what the bot makes of a pull request's head (reads only) ----------------------------
def examine(ctx, git, pr, st, reserved=()):
    """{kind, entry, info, reasons}: kind is ignored (not into main), organiser, closed, draft, held,
    moved (the head changed while it was read), invalid or valid."""
    n = pr["number"]
    author = (pr.get("user") or {}).get("login") or "ghost"
    if (pr.get("base") or {}).get("ref") != ctx.default_branch:
        return {"kind": "ignored"}
    files = ctx.gh.pr_files(n) if (pr.get("changed_files") or 0) <= 3000 else None
    root, reasons, outside = precheck.paths_rule(files)
    if outside and ctx.gh.permission(author) in ORGANISER:
        return {"kind": "organiser"}
    if pr.get("state") != "open":
        return {"kind": "closed"}
    if pr.get("draft"):
        return {"kind": "draft"}
    if "hold" in _labels(pr):
        return {"kind": "held"}
    sha = (pr.get("head") or {}).get("sha") or ""
    if not SHA_RE.match(sha):
        raise ValueError("the pull request's head is not a full SHA")
    got = None
    for k in range(4):
        got = git.fetch(f"refs/pull/{n}/head")
        if got == sha:
            break
        ctx.sleep(5 * (k + 1))
    if got != sha:
        if ctx.gh.pr(n)["head"]["sha"] != sha:
            return {"kind": "moved"}
        raise RuntimeError(f"refs/pull/{n}/head is {got}, the API says {sha}")
    eid = entry_id(n, sha)
    info = {}
    # the author is the pull request's opener, and the head must be in the author's own repository:
    # anyone can open a pull request from another user's public branch, and so be first with a root
    # that user has not submitted yet (the copy rule's order)
    head_owner = (((pr.get("head") or {}).get("repo") or {}).get("owner") or {}).get("login")
    if head_owner != author:
        reasons.append(f"the head branch is in {clean(head_owner or 'a deleted repository', 40)}'s repository, not the "
                       f"author's ({clean(author, 40)}): open the pull request from a branch of your own fork")
    if root:
        if root in reserved:
            reasons.append(f"submissions/{root}/ is a directory the organiser keeps on main; choose another root name")
        more, info = precheck.tree_rule(git, sha, root)
        reasons = reasons + more
    agent, builds = precheck.notes_header(info["notes"], n) if info.get("notes") else (None, [])
    entry = {"id": eid, "pr": n, "sha": sha, "root": root or "",
             "author": author if LOGIN_RE.match(author) else clean(author, 40),
             "title": clean(pr.get("title"), 200), "agent": agent, "builds_on": builds,
             "opened": pr.get("created_at"), "queued": None, "started": None, "finished": None, "attempts": 0,
             "status": "queued", "verdict": None, "score": None, "comparable": False, "truncated": False,
             "reasons": [], "run_url": None, "tag": f"rf-source/{eid}",
             "notes": f"notes/{eid}.md" if info.get("notes") else None,
             "readme": f"readme/{eid}.md" if info.get("readme") else None,
             "record_of": None, "tree": info.get("tree"), "prover_tree": info.get("prover_tree"), "verified": False,
             "harness_commit": None, "prover_sha256": None}
    if files is None or any(str(f.get(k) or "").startswith(".github/") for f in files
                            for k in ("filename", "previous_filename")):
        # main's workflow check on the head's workflows, read as data
        reasons += [f"workflow check: {p}" for p in wfcheck.check_git_limited(git.dir, sha)][:10]
    if not reasons:
        dup = rfqueue.duplicate_of(st, eid, n, entry["author"], entry["tree"], entry["prover_tree"])
        if dup:
            reasons.append(dup)
    reasons = [clean(r, 300) for r in reasons[:20]]
    if reasons:
        entry.update(tag=None, notes=None, readme=None)
    return {"kind": "invalid" if reasons else "valid", "entry": entry, "info": info, "reasons": reasons}


def admit(ctx, git, x, force=False):
    """The intake's writes for an examined head (none on `data`): the retention tag and the pending
    "queued" status (valid), or the failure status (invalid), and one comment. A head the bot has
    already admitted is left alone unless `force` (the owner's re-intake). Returns the head's queue
    timestamp (the status's time) or None."""
    e = x["entry"]
    prior = bot_statuses(ctx, e["sha"])
    if prior and not force and not prior[0].get("description", "").startswith(READMIT):
        return None
    if x["kind"] == "valid" and not git.create_tag(e["sha"], e["tag"]):
        x["kind"], x["reasons"] = "invalid", [f"the retention tag {e['tag']} exists at another commit"]
        e.update(tag=None, notes=None, readme=None)
    if x["kind"] == "valid":
        ctx.gh.set_status(e["sha"], "pending", "queued", f"{ctx.server}/{ctx.repo}/pull/{e['pr']}")
        if not prior:
            _try(ctx, "comment", ctx.gh.comment, e["pr"], render.intake_comment(dict(e, status="queued"), None, None))
    else:
        e2 = dict(e, status="invalid", reasons=x["reasons"])
        ctx.gh.set_status(e["sha"], *render.status_for(e2), f"{ctx.server}/{ctx.repo}/pull/{e['pr']}")
        _try(ctx, "comment", ctx.gh.comment, e["pr"], render.intake_comment(e2, None, None))
    return ctx.now()


# ---- intake -------------------------------------------------------------------------------------
def intake(ctx, pr_n, force=False):
    """Prechecks the pull request's current head and admits it (tag, status, comment), then
    dispatches `sync`. Writes nothing on `data`. Returns what it found."""
    pr = ctx.gh.pr(pr_n)
    git = ctx.git()
    st = _state(ctx, git.snapshot(DATA))       # fails closed: an unreadable `data` stops the intake
    x = examine(ctx, git, pr, st, _reserved(git, st))
    wf = workflow_problems(ctx, git, pr) if x["kind"] == "organiser" else []
    if wf:              # an organiser's pull request: status and comment (a submission's head: examine)
        sha = pr["head"]["sha"]
        _try(ctx, "status", ctx.gh.set_status, sha, "failure", "workflow check failed (wfcheck.py)",
             f"{ctx.server}/{ctx.repo}/pull/{pr_n}")
        _try(ctx, "comment", ctx.gh.comment, pr_n, render.workflow_comment(sha, wf))
    if x["kind"] in ("valid", "invalid"):
        admit(ctx, git, x, force)
    if x["kind"] not in ("ignored", "organiser"):
        _try(ctx, "dispatch sync", ctx.gh.dispatch, "sync.yml", ctx.default_branch)
    ctx.log(f"intake: #{pr_n}: {x['kind']}")
    return x["kind"]


def workflow_problems(ctx, git, pr):
    """The workflow check (`wfcheck.check_git`, `main`'s code) on the head of an open pull
    request into `main` whose files touch `.github/`, read as data; its problems, or [] (a PR whose
    file list the API cannot give is checked too). It cannot be edited away by the pull request,
    unlike pin-check's PR job."""
    n = pr["number"]
    if pr.get("state") != "open" or (pr.get("base") or {}).get("ref") != ctx.default_branch:
        return []
    files = ctx.gh.pr_files(n) if (pr.get("changed_files") or 0) <= 3000 else None
    touches = files is None or any(str(f.get(k) or "").startswith(".github/")
                                   for f in files for k in ("filename", "previous_filename"))
    if not touches:
        return []
    sha = (pr.get("head") or {}).get("sha") or ""
    if not SHA_RE.match(sha) or git.fetch(f"refs/pull/{n}/head") != sha:
        return []                          # it moved: the next event checks the new head
    return wfcheck.check_git_limited(git.dir, sha)


def intake_failed(ctx, pr_n):
    """After an exception in the intake: the head's status says so (sync retries it)."""
    try:
        sha = ctx.gh.pr(pr_n)["head"]["sha"]
        ctx.gh.set_status(sha, "error", "intake failed; the bot retries it", ctx.run_url)
    except Exception as ex:  # noqa: BLE001
        ctx.log(f"intake_failed: {ex}")


def _reserved(git, st):
    roots = {e["root"] for e in rfqueue.records(st)}
    return main_roots(git) - roots


# ---- sync: the single writer of new queue entries ------------------------------------------------
def sync(ctx):
    """Brings `data` up to date with GitHub: every open pull request's head is queued (with its
    NOTES/README copied from the retention tag) or invalid; older heads are superseded; closed,
    draft, held and organiser pull requests' queued entries are withdrawn; superseded and withdrawn
    heads get their commit status. Idempotent. Returns the number of entries changed."""
    git = ctx.git()
    st0 = _state(ctx, git.snapshot(DATA))
    reserved = _reserved(git, st0)
    prs = {p["number"]: p for p in ctx.gh.open_prs()}
    looks, admitted, t0, more = {}, {}, ctx.monotonic(), []
    for n, pr in sorted(prs.items()):
        if (pr.get("base") or {}).get("ref") != ctx.default_branch or pr.get("draft") or "hold" in _labels(pr):
            continue
        sha = pr["head"]["sha"]
        old = rfqueue.find(st0, entry_id(n, sha)) if SHA_RE.match(sha or "") else None
        if old and old["status"] not in ("withdrawn", "superseded", "invalid"):
            continue
        prior = bot_statuses(ctx, sha)
        if old and old["status"] == "invalid" and not (prior and prior[0].get("description") == "queued"):
            continue                       # an invalid head stays invalid unless re-admitted
        if ctx.monotonic() - t0 > SYNC_BUDGET_S:
            more.append(n)                 # the next sync (dispatched below) examines it
            continue
        try:
            full = ctx.gh.pr(n)            # changed_files is only in the single-PR payload
            x = examine(ctx, git, full, st0, reserved)
        except Exception as ex:  # noqa: BLE001 - one unreadable pull request must not stop the others
            ctx.log(f"sync: #{n} not examined ({ex.__class__.__name__}: {str(ex)[:120]}); next sync retries")
            continue
        if x["kind"] not in ("valid", "invalid"):
            looks[n] = x
            continue
        # the head's status must say what the bot found: a valid head "queued" (whose time is the
        # queue time), an invalid one "invalid…"; otherwise (no intake ran, it failed, or the fresh
        # state disagrees with it) sync admits the head itself
        want = "queued" if x["kind"] == "valid" else "invalid"
        top = prior[0].get("description", "") if prior else ""
        if (top == "queued") if want == "queued" else top.startswith("invalid"):
            q = prior[0]["created_at"]
        else:
            try:
                q = admit(ctx, git, x, force=True)
            except Exception as ex:  # noqa: BLE001
                ctx.log(f"sync: #{n} not admitted ({ex.__class__.__name__}: {str(ex)[:120]}); next sync retries")
                continue
        admitted[n] = (x, q)
    closed = {}
    for e in st0["submissions"]:
        if e["status"] == "queued" and e["pr"] not in prs and e["pr"] not in closed:
            try:
                closed[e["pr"]] = ctx.gh.pr(e["pr"])
            except Exception as ex:  # noqa: BLE001
                ctx.log(f"sync: #{e['pr']} unreadable ({ex.__class__.__name__}); kept")
    effects, changed = [], []

    def mutate(snap):
        st = _state(ctx, snap)
        now = ctx.now()
        effects.clear()
        changed.clear()
        before = {e["id"]: e["status"] for e in st["submissions"]}
        ch, extra = Changes(), {}
        for n, (x, q) in sorted(admitted.items(), key=lambda kv: (kv[1][1], kv[0])):
            e = copy.deepcopy(x["entry"])
            e["builds_on"] = [b for b in e.get("builds_on") or [] if rfqueue.of_pr(st, b)]
            if x["kind"] == "valid":
                dup = rfqueue.duplicate_of(st, e["id"], n, e["author"], e["tree"], e.get("prover_tree"))
                if dup:
                    e.update(tag=None, notes=None, readme=None)
                    e, _c = rfqueue.add_invalid(st, e, [dup], q)
                    effects.append(("invalid", copy.deepcopy(e)))
                    continue
                e, _c = rfqueue.enqueue(st, e, q)
                if e["status"] == "queued":
                    for k, src in (("notes", "notes"), ("readme", "readme")):
                        if e.get(k) and x["info"].get(src):
                            ch.put(e[k], x["info"][src])
                            extra[e[k]] = x["info"][src]
            else:
                rfqueue.add_invalid(st, e, x["reasons"], q)
        for n, pr in prs.items():
            sha = (pr.get("head") or {}).get("sha") or ""
            if (pr.get("base") or {}).get("ref") != ctx.default_branch:
                continue
            kind = (looks.get(n) or {}).get("kind")
            if pr.get("draft") or kind == "draft":
                rfqueue.withdraw(st, n, now, "the pull request is a draft")
                continue
            if "hold" in _labels(pr) or kind == "held":
                rfqueue.withdraw(st, n, now, "the pull request is on hold (label hold)")
                continue
            if kind == "organiser":
                rfqueue.withdraw(st, n, now, "an organiser pull request")
                continue
            for e in rfqueue.of_pr(st, n):
                if e["status"] == "queued" and e["sha"] != sha and not rfqueue.confirming(e):
                    e.update(status="superseded", finished=now,
                             reasons=["the pull request moved before this commit was evaluated"])
        for n, pr in closed.items():
            if pr.get("state") != "open":
                rfqueue.withdraw(st, n, now, "the pull request was closed before its evaluation")
        for path in rfqueue.compact(st):
            ch.put(path, None)
        for e in st["submissions"]:
            if before.get(e["id"]) != e["status"]:
                changed.append(e["id"])
                if e["status"] in ("superseded", "withdrawn") and before.get(e["id"]) is not None:
                    effects.append(("status", copy.deepcopy(e)))
        stale = bool(st.get("_stale"))
        if not changed and ch.empty() and snap.head and not stale:
            return None                    # (an absent `data` is created, with an empty state)
        _write_state(ctx, ch, snap, st, extra)
        effects.append(("queued?", rfqueue.any_queued(st) or rfqueue.due_port(st, ctx.pin) is not None))
        if stale:
            effects.append(("main", copy.deepcopy(st)))
        return ch
    git.transact(DATA, mutate, "sync")
    for kind, e in effects:
        if kind == "status":
            st_, desc = render.status_for(e)
            _try(ctx, "status", ctx.gh.set_status, e["sha"], st_, desc, None)
        elif kind == "invalid":
            _try(ctx, "status", ctx.gh.set_status, e["sha"], *render.status_for(e), None)
            _try(ctx, "comment", ctx.gh.comment, e["pr"], render.intake_comment(e, None, None))
        elif kind == "queued?" and e:
            _try(ctx, "dispatch", ctx.gh.dispatch, "evaluate-next.yml", ctx.default_branch)
        elif kind == "main":
            _try(ctx, "sync main", sync_main, ctx, e)
    if more:
        ctx.log(f"sync: the time budget ({SYNC_BUDGET_S} s) ran out before #{more[0]} ({len(more)} heads left): "
                "the next sync goes on")
        _try(ctx, "dispatch sync", ctx.gh.dispatch, "sync.yml", ctx.default_branch)
    ctx.log(f"sync: {len(changed)} entries changed")
    return len(changed)


# ---- select -------------------------------------------------------------------------------------
def select(ctx, force_pr=None, retire_id=None, resume=False, retire_track=None):
    """Picks the next entry (`rfqueue.order`, AGENTS.md §9; `force_pr`: that pull request's waiting
    or errored entry), marks it running, and returns a copy of it (None: nothing to evaluate). Entries a
    previous run left running are reaped first (runs are serialised by `rf-eval`). `retire_id`: the
    owner retires that record in the track `retire_track` first. When a track has no record standing
    at the pin and its last record is of an earlier pin, that record's port to this pin is created
    and evaluated before anything else, forced runs included, so no other entry can take the record
    before it; with two such tracks, one port after the other (one for both if one entry holds both).
    `resume`: the owner clears a pause (and the error streak) first. A `retire_id` that retires
    nothing (not a record of that track, or already retired in it) raises after writing nothing."""
    live, picked, notify, final = {}, {}, {}, {}

    def live_pr(n):
        if n not in live:
            try:
                live[n] = ctx.gh.pr(n)
            except Exception as ex:  # noqa: BLE001 - one unreadable pull request must not stop the queue
                ctx.log(f"select: #{n} unreadable ({ex.__class__.__name__}); skipped")
                live[n] = None
        return live[n]

    def mutate(snap):
        st = _state(ctx, snap)
        now = ctx.now()
        picked.clear()
        notify.clear()
        final.pop("retire_failed", None)
        changed = bool(st.get("_stale"))      # a pin move: rewrite the pin and its record at once
        if retire_id:
            r = rfqueue.find(st, retire_id)
            if r is None or not rfqueue.retire(r, retire_track, now, "retired by the owner"):
                # the owner's retirement did nothing (a wrong id or track): change nothing, start
                # nothing, and fail the run so the owner sees it
                final["retire_failed"] = True
                return None
            changed = True
        if resume and (st.get("paused") or st.get("error_streak")):
            rfqueue.clear_errors(st)
            ctx.log("select: the owner cleared the pause")
            changed = True
        reaped, paused = rfqueue.reap(st, now)
        notify.update({i: copy.deepcopy(rfqueue.find(st, i)) for i in reaped})
        changed = changed or bool(reaped)
        final["paused"] = paused
        cands = rfqueue.order(st)
        due = rfqueue.due_port(st, ctx.pin)
        if st.get("paused") and force_pr is None:
            # the error streak paused the queue (common.py): nothing runs until the owner forces a
            # run, whose clean verdict resumes it
            cands, due = [], None
            ctx.log(f"select: the queue is paused since {st['paused'].get('since')}: {st['paused'].get('reason')}")
        # a waiting port (re-queued after an ERROR) or confirmation run is still first
        ports = [e for e in cands if (e.get("port_of") or rfqueue.confirming(e)) and e["status"] == "queued"]
        if due is not None:
            cands, changed = [rfqueue.port(st, due["pr"], ctx.pin, now, o=due)], True
        elif ports:
            cands = ports[:1]
        elif force_pr is not None:
            cands = [e for e in cands if e["pr"] == force_pr]
            if not cands:
                errs = [e for e in rfqueue.of_pr(st, force_pr) if e["status"] == "error"]
                if errs:
                    e = max(errs, key=lambda e: e.get("finished") or "")
                    e.update(status="queued", finished=None, attempts=0)
                    cands, changed = [e], True
                else:
                    port = rfqueue.port(st, force_pr, ctx.pin, now)
                    if port:
                        cands, changed = [port], True
        for e in cands:                      # every candidate, so one unreadable PR blocks nothing
            p = (live_pr(e["pr"]) if not (e.get("port_of") or rfqueue.confirming(e))
                 else {"state": "open", "head": {"sha": e["sha"]}})
            if p is None:
                continue
            if p.get("state") != "open":
                e.update(status="withdrawn", finished=now, reasons=["the pull request was closed before its evaluation"])
                notify[e["id"]] = copy.deepcopy(e)
                changed = True
                continue
            if (p.get("head") or {}).get("sha") != e["sha"]:
                e.update(status="superseded", finished=now,
                         reasons=["the pull request moved before this commit was evaluated"])
                notify[e["id"]] = copy.deepcopy(e)
                changed = True
                continue
            if force_pr is None and not rfqueue.confirming(e) and (p.get("draft") or "hold" in _labels(p)):
                continue
            rfqueue.mark_running(e, now, ctx.run_url)
            e["run_attempt"] = ctx.run_attempt
            recs = [r for r in rfqueue.standing(st, ctx.pin).values() if r]
            rec = max(recs, key=lambda r: (r.get("finished") or "", r["id"]), default=None)
            picked.update(copy.deepcopy(e))
            picked["record_cache"] = e.get("record_cache") is not False
            # the record build cache may only be restored with the attested manifest of the newest
            # standing record (of either track: the cache holds the build of the newest record taken)
            picked["record_manifest"] = (rec or {}).get("build_manifest") or ""
            changed = True
            break
        final.update(state=copy.deepcopy(st))
        if not changed:
            return None
        ch = Changes()
        _write_state(ctx, ch, snap, st)
        return ch
    ctx.git().transact(DATA, mutate, "select")
    if final.get("retire_failed"):
        raise RuntimeError(f"select: {retire_id} is not a standing or earlier record of the track {retire_track!r} "
                           "(or is already retired in it): nothing retired, nothing evaluated")
    try:
        sync_main(ctx, final["state"])    # heals a record a failed publish left off main
    except Exception as ex:  # noqa: BLE001 - never block the queue on it; publish raises it
        ctx.log(f"select: main is not synced to the record: {ex}")
    for e in notify.values():
        st_, desc = render.status_for(e)
        _try(ctx, "status", ctx.gh.set_status, e["sha"], st_, desc, e.get("run_url"))
    if final.get("paused") and not _try(ctx, "notice", ctx.gh.issue, render.PAUSE_TITLE,
                                        render.pause_notice(final["state"], ctx.run_url)) and not picked:
        raise RuntimeError("select: the queue paused after a reaped run, but the owner's notice failed")
    if not picked:
        ctx.log("select: nothing to evaluate")
        return None
    e = picked
    if not (ID_RE.match(e["id"]) and SHA_RE.match(e["sha"]) and ROOT_RE.match(e["root"])):
        raise ValueError(f"select: a malformed entry {e['id']!r}")
    git = ctx.git()
    if git.remote_ref(f"refs/tags/{e['tag']}") != e["sha"]:
        raise RuntimeError(f"select: the retention tag {e['tag']} is not at {e['sha']}")
    _try(ctx, "status", ctx.gh.set_status, e["sha"], "pending", "evaluating", ctx.run_url)
    return e


# ---- publish ------------------------------------------------------------------------------------
def load_result(path, cap=16 << 20):
    """(raw bytes, parsed dict) of result.json, or (None, None)."""
    try:
        with open(path, "rb") as f:
            raw = f.read(cap + 1)
        if len(raw) > cap:
            return None, None
        r = json.loads(raw)
        return (raw, r) if isinstance(r, dict) else (None, None)
    except (OSError, ValueError, RecursionError):
        return None, None


def publish(ctx, eid, result_path):
    """Publishes the verdict of the running entry `eid` (this run's): its status, the result on
    `data`, the record on `main`, the comment and the commit status; then dispatches the next
    evaluation if anything is queued. Returns the entry (None if this run does not own it)."""
    raw, result = load_result(result_path) if result_path else (None, None)
    st0 = _state(ctx, ctx.git().snapshot(DATA))
    e0 = rfqueue.find(st0, eid) or {}
    if result is None:
        ver = {"attested": False, "record_ok": False, "reason": "no result"}
    else:
        ver = ctx.verify(result_path, result, e0.get("run_attempt") or 1)
        why = entry_mismatch(result, e0, ctx.repo)
        if why:     # the attested result measured another commit than the one selected: the organiser's
            ver = {"attested": False, "record_ok": False, "reason": why}
    done = {}

    def mutate(snap):
        st = _state(ctx, snap)
        done.clear()
        e = rfqueue.find(st, eid)
        if e is None or e["status"] != "running" or e.get("run_url") != ctx.run_url:
            return None
        rids = {t: r["id"] if r else None for t, r in rfqueue.standing(st, ctx.pin).items()}
        # the records of other commits with this prover (binary or sources; every port of a record
        # shares its commit, and keeps its crowns): one that is this author's, or was queued first,
        # bars this entry; another author's queued after this author first showed the prover is a
        # copy, set aside (rfqueue.prover_owner: the earliest-queued owner of a prover wins)
        keys = (result_prover_keys(result) if ver.get("attested") else set()) | {
            k for k in rfqueue.prover_keys(e) if k[0] == "prover_tree"}
        provers, aside = rfqueue.prover_owner(st, e, keys)
        recs = rfqueue.standing(st, ctx.pin, aside)
        d = decide(result, ver, ctx.pin, recs, e.get("attempts", 1), provers, tracks=e.get("port_tracks"))
        now = ctx.now()
        if aside and d["verified"] and d["verdict"] == "ACCEPT":
            d["reasons"] = d["reasons"][:19] + [
                f"the record {', '.join(aside)} has this prover, but another author's entry queued after this author "
                "first showed it: set aside, this entry is compared as if it had not been taken (the earliest-queued "
                "owner of a prover wins)"]
        # the retry without the record build cache of a REJECT at a badge check (decide.cache_check):
        # if the clean rebuild's badge is byte-identical to the first run's, the cache cannot have
        # caused the failed check, so the first run's REJECT stands and this run's score is discarded
        pend = e.get("cache_check")
        stood = False
        if pend and not d["requeue"] and not d["organiser_side"]:
            e.pop("cache_check", None)
            if cache_check_stands(pend, result):
                stood, every_t = True, list(d["record_of"])
                d.update(verdict="REJECT", status="rejected", score=None, took=[], requeue=False, comparable=False,
                         record_of={t: None for t in every_t}, against={t: None for t in every_t},
                         reasons=(pend.get("reasons") or [])[:18] + [
                             f"the evaluation without the record build cache ({ctx.run_url}) built a byte-identical "
                             "badge, so the cache could not have caused the failed check: the first run's REJECT "
                             f"({pend.get('run_url')}) stands, and this run's verdict and score are discarded"])
            elif pend.get("badge_sha256") and badge_sha(result):
                # the clean rebuild built another badge than the first run's: the badge build is not
                # reproducible, or the cache held another build. Either is the organiser's question,
                # never a second draw for the entry: it waits in `error` for the owner (a forced run)
                every_t = list(d["record_of"])
                d.update(status="error", took=[], requeue=False, record_of={t: None for t in every_t},
                         against={t: None for t in every_t},
                         reasons=(pend.get("reasons") or [])[:17] + [
                             f"organiser question: the evaluation without the record build cache ({ctx.run_url}) "
                             f"built another badge than the first run's ({pend.get('run_url')}), whose check was "
                             f"rejected; this run's verdict is {d['verdict']}",
                             "held for the owner (status error): the owner decides, and a forced run evaluates it again"])
            else:
                d["reasons"] = d["reasons"][:19] + ["the evaluation without the record build cache: a badge is unknown "
                                                    "on one side, so this run's verdict stands"]
        # the confirmation (decide.py): a pending candidate of this pin is decided by this run too; one
        # of an earlier pin is void (the pin moved before it ran), and this run is a first run again
        first = e.get("confirm") if (e.get("confirm") or {}).get("pin") == ctx.pin else None
        e.pop("confirm", None)
        conf = confirmed(first, d) if first else None
        if first and conf and d["status"] == "rejected" and cache_retry(result, e, d["verified"]):
            conf = None                         # a REJECT that used the record build cache: confirmed again without it
            d.update(requeue=True, status="queued")
            e["record_cache"] = False
            if cache_check(result, ctx.run_url, d["reasons"]):
                e["cache_check"] = cache_check(result, ctx.run_url, d["reasons"])
            d["reasons"] = d["reasons"][:19] + ["the record build cache was used: the confirmation runs once more without it"]
        if first and conf is None:
            e["confirm"] = first                # an organiser-side end: the confirmation stays pending
        elif conf:
            d.update(conf, reasons=(d["reasons"] + conf["reasons"])[-20:])
            e["confirmation"] = {"first_run": first.get("run_url"), "first_result": first.get("result"),
                                 "run": ctx.run_url, "result": f"results/{eid}-confirm.json",
                                 "first_score": first.get("score"), "score": d2_score(result),
                                 "status": conf["status"], "score_run": conf["score_run"]}
        elif d["status"] == "record" and not e.get("port_of"):
            # a record candidate: queued once more at this pin, ahead of the queue (rfqueue.order)
            e["confirm"] = candidate(d, ctx.pin, ctx.run_url, f"results/{eid}.json")
            d.update(requeue=True, status="queued", took=[])
            d["reasons"] = d["reasons"][:19] + [f"a record candidate in {', '.join(e['confirm']['took'])}: queued for its "
                                                "confirmation run (this commit, once more at this pin); the record is "
                                                "taken only if that run also beats the standing record"]
        ps = result.get("prover_sha256") if isinstance(result, dict) else None
        e["build_manifest"] = build_manifest_sha(result) if d["verified"] else None
        e.update({k: d[k] for k in ("verdict", "score", "comparable", "truncated", "harness_commit",
                                    "verified", "record_of", "against", "reasons")}, record_in=[], retired_in={},
                 prover_sha256=ps if isinstance(ps, str) and len(ps) == 64 and ps.isalnum() else None,
                 prover_sources_sha256=dict(result_prover_keys(result)).get("prover_sources_sha256") if d["verified"] else None)
        # does this run count as the author's start in the fair order? a named organiser error never does
        # (a run with no result at all is not a named organiser error: it may be the entry's doing, so
        # it counts as an unnamed ERROR does, from the entry's second one)
        rfqueue.settle_run(e, d["organiser_error"] if result is not None else None,
                           error=d["verdict"] == "ERROR" or not d["verified"])
        if d["organiser_error"] in PAUSING_ERRORS:
            e["attempts"] = max(0, e.get("attempts", 1) - 1)      # the organiser's fault: not an attempt
        if d["organiser_side"]:
            # any run that ended on the organiser's side joins the error streak (common.py: the pause);
            # no readable result (the attest job did not finish after entry code ran, or result.json
            # could not be read: too large, not JSON, not an object) counts once per author, like
            # `harness`
            kind = "noresult" if result is None else d["organiser_error"] or "unnamed"
            if rfqueue.note_error(st, e, kind, now, d["error_reason"] or kind, ctx.run_url):
                done["paused"] = True
        elif d["benchmarked"] and rfqueue.clear_errors(st):
            # only a clean verdict whose stream ran on the season's machine clears the streak and
            # resumes: a REJECT before or inside the stream never reached the benchmark-side checks
            # (the service cache, the stream harness, the lengths, the drift) and leaves it as it is
            done["resumed"] = True
        ch = Changes()
        keep_raw = raw is not None and len(raw) <= 4 << 20
        if d["status"] != "queued" and not e.get("confirm") and cache_retry(result, e, d["verified"]):
            d["requeue"] = True
            e["reasons"] = e["reasons"][:19] + ["the record build cache was used: evaluated once more without it"]
            if cache_check(result, ctx.run_url, e["reasons"]):
                e["cache_check"] = cache_check(result, ctx.run_url, e["reasons"])
        if d["requeue"]:
            if d["verdict"] in ("ERROR", "REJECT") or not d["verified"]:
                e["record_cache"] = False      # the retry builds clean: a sabotaged cache cannot fail it
            e.update(status="queued", finished=None)
            if e.get("confirm") and e["confirm"].get("run_url") == ctx.run_url:
                e["attempts"] = 0              # the confirmation run has its own retry, as a port does
        else:
            e.update(status=d["status"], finished=now, record_in=d["took"])
            if d["status"] == "record":
                for rid in aside:      # a copy of this prover: retired in the tracks this entry takes
                    r = rfqueue.find(st, rid)
                    for t in d["took"]:
                        rfqueue.retire(r, t, now, f"retired: its prover is that of {eid}, whose author showed it first")
        done["record_changed"] = {t: r["id"] if r else None for t, r in rfqueue.standing(st, ctx.pin).items()} != rids
        if keep_raw and stood:
            # the retry whose verdict was discarded: kept beside the first run's, which stays the entry's result
            ch.put(f"results/{eid}{'-confirm' if first else ''}-nocache.json", raw)
        elif keep_raw and first:
            ch.put(f"results/{eid}-confirm.json", raw)     # the first run's result stays results/<id>.json
        elif keep_raw:
            ch.put(f"results/{eid}.json", raw)
            e["result"] = f"results/{eid}.json"
        if conf and e["status"] != "queued":
            # the entry's run and result are the run its score is from (decide.confirmed: `score_run`),
            # so that the Actions link and the result JSON a reader opens are the same run's
            if conf["score_run"] == "confirmation" and keep_raw:
                e["result"], e["run_url"] = f"results/{eid}-confirm.json", ctx.run_url
            elif conf["score_run"] == "first":
                e["result"], e["run_url"] = first.get("result") or e.get("result"), first.get("run_url") or e["run_url"]
        _write_state(ctx, ch, snap, st)
        done.update(entry=copy.deepcopy(e), state=copy.deepcopy(st))
        return ch
    ctx.git().transact(DATA, mutate, f"publish {eid}")
    changed_record = done.pop("record_changed", False)
    paused, resumed = done.pop("paused", False), done.pop("resumed", False)
    if not done:
        ctx.log(f"publish: {eid} is not running under this run; nothing published")
        return None
    e, st = done["entry"], done["state"]
    failed = []
    if not _try(ctx, "status", ctx.gh.set_status, e["sha"], *render.status_for(e), ctx.run_url):
        failed.append("status")
    if not _try(ctx, "comment", ctx.gh.comment, e["pr"], render.publish_comment(e, ctx.run_url)):
        failed.append("comment")
    if (e["status"] == "record" or changed_record) and not _try(ctx, "sync main", sync_main, ctx, st):
        failed.append("main")
    if paused and not _try(ctx, "notice", ctx.gh.issue, render.PAUSE_TITLE, render.pause_notice(st, ctx.run_url)):
        failed.append("notice")
    if resumed:
        ctx.log("publish: the queue is no longer paused")
    if rfqueue.any_queued(st) and not st.get("paused") and not _try(ctx, "dispatch", ctx.gh.dispatch, "evaluate-next.yml",
                                                                    ctx.default_branch):
        failed.append("dispatch")
    if failed:
        raise RuntimeError(f"publish: {eid} is published on data, but these failed: {', '.join(failed)}")
    return e


def entry_mismatch(result, e, repo):
    """Why an attested result is not of the selected entry `e`, or None. A core that names the
    commit it measured (`entry.sha`, `entry.tree`: the tree of `submissions/<root>`) must name `e`'s,
    and then its `entry.name` must be `<repo>:submissions/<root>`; a result of an older core, with
    neither field, is not compared."""
    ent = result.get("entry") if isinstance(result, dict) else None
    if not isinstance(ent, dict) or (ent.get("sha") is None and ent.get("tree") is None):
        return None
    if ent.get("sha") is not None and ent.get("sha") != e.get("sha"):
        return f"the result measured the commit {clean(ent.get('sha'), 40)}, not the selected {e.get('sha')}"
    if ent.get("tree") is not None and ent.get("tree") != e.get("tree"):
        return f"the result measured the tree {clean(ent.get('tree'), 40)}, not the selected root's {e.get('tree')}"
    name = ent.get("name")
    if name is not None and name != f"{repo}:submissions/{e.get('root')}":
        return f"the result names the entry {clean(name, 80)}, not {repo}:submissions/{e.get('root')}"
    return None


def d2_score(result):
    """The cleaned score of a confirmation run's result (for the entry's `confirmation` record)."""
    from decide import clean_score
    return clean_score(result.get("score")) if isinstance(result, dict) else None


def sync_main(ctx, st):
    """Makes `main` hold the standing records: their checked roots (the trees at their retained
    commits, replacing the roots of earlier records) and `records.json`, which names the pin and the
    standing record of each track whatever happens. With no record standing in any track, only
    `records.json` changes and the last records' roots stay until a new record replaces them. When
    two standing records of different entries share a root name, the newer record's tree is the one
    on `main` (the other stays at its tag). A no-op if `main` already says so."""
    recs = {r["id"]: r for r in rfqueue.standing(st, ctx.pin).values() if r}
    recs = sorted(recs.values(), key=lambda r: (r.get("finished") or "", r["id"]))      # oldest first: the newest wins a root
    want = render.records_json(st, ctx.pin)
    git = ctx.git()
    if not recs:
        def mutate_none(snap):
            if snap.read("records.json", 16 << 20) == want:
                return None
            ch = Changes()
            ch.put("records.json", want)
            return ch
        return git.transact(ctx.default_branch, mutate_none, f"records: no record stands at the pin {ctx.pin[:12]}")
    trees = {}
    for rec in recs:
        commit = git.fetch(f"refs/tags/{rec['tag']}", local="refs/rf/record")
        if commit != rec["sha"]:
            raise RuntimeError(f"sync_main: the tag {rec['tag']} is at {commit}, the record is {rec['sha']}")
        tree = git.tree_of(commit, f"submissions/{rec['root']}")
        if tree is None or (rec.get("tree") and tree != rec["tree"]):
            raise RuntimeError(f"sync_main: the root of {rec['id']} at its tag is not the root that was checked")
        trees[rec["root"]] = tree             # a shared root name: the newer record's tree only
    roots = set(trees)

    def mutate(snap):
        cur = snap.read("records.json", 16 << 20)
        if cur == want:
            return None
        olds = set()
        try:
            j = json.loads(cur or b"null") or {}
            rec_, hist = j.get("record"), j.get("history") or []
            # version 2: {track: record} and {track: [records]}; version 1: one record and one list
            rs = list(rec_.values()) if isinstance(rec_, dict) and "id" not in rec_ else [rec_]
            for h in (hist.values() if isinstance(hist, dict) else [hist]):
                rs += list(h) if isinstance(h, list) else []
            for r in rs:
                if isinstance(r, dict) and isinstance(r.get("root"), str) and ROOT_RE.match(r["root"]):
                    olds.add(r["root"])
        except (ValueError, AttributeError, TypeError):
            pass
        ch = Changes()
        for old in sorted(olds - roots):
            ch.drop_dir(f"submissions/{old}")
        for root, tree in sorted(trees.items()):
            ch.drop_dir(f"submissions/{root}")
            ch.graft(f"submissions/{root}", tree)
        ch.put("records.json", want)
        return ch
    what = "; ".join(f"{', '.join(t for t, r in rfqueue.standing(st, ctx.pin).items() if r and r['id'] == rec['id'])}: "
                     f"{rec['root']} ({rec['id']}, {render.scores_text(rec.get('score'))}) by {rec['author']}"
                     for rec in recs)
    return git.transact(ctx.default_branch, mutate, f"records: {what}, evaluated in "
                        + ", ".join(dict.fromkeys(str(r.get("run_url")) for r in recs)))


def record_build(ctx, result, build_dir, pin, eid):
    """Whether the downloaded `entry-build` artifact of a new record may be cached: its
    manifest.json's sha256 is the attested `entry_build.manifest_sha256`. If so, deletes the older
    `rf-record-build-<pin>-*` caches (the new one is saved by the workflow under the returned key)."""
    import hashlib
    import os
    want = build_manifest_sha(result)
    try:
        with open(os.path.join(build_dir, "manifest.json"), "rb") as f:
            got = hashlib.sha256(f.read()).hexdigest()
    except OSError:
        got = None
    if not want or got != want:
        ctx.log(f"record-build: not cached (manifest {got}, attested {want})")
        return None
    key = f"rf-record-build-{pin}-{eid}"
    for c in ctx.gh.caches(f"rf-record-build-{pin}-"):
        if c.get("key") != key and str(c.get("key", "")).startswith(f"rf-record-build-{pin}-"):
            ctx.gh.delete_cache(c["key"])
    return key
