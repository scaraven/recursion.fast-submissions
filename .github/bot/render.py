"""What the bot writes for people (TRUSTED; pure): pull-request comments, commit-status
descriptions, `notes.md` on `data` and `records.json` on `main`. Untrusted text appears only in
code spans (comments) or inside a fence longer than any it contains (notes.md)."""
import json
import re

from common import MARGIN, STREAK_WINDOW_S, TRACKS, ascii_line, code_span, is_num, score_fields
import rfqueue

STATE = {"record": "success", "accepted": "success", "unranked": "success", "provisional": "failure",
         "rejected": "failure", "invalid": "failure", "error": "pending", "queued": "pending", "running": "pending",
         "retired": "success"}
WORDS = {"record": "new record", "accepted": "accepted (did not beat the record)",
         "unranked": "accepted, not comparable (not ranked)", "provisional": "provisional (never ranked)",
         "rejected": "rejected", "error": "waiting on the organiser (an organiser-side error)", "invalid": "invalid submission",
         "queued": "queued", "running": "evaluating", "superseded": "superseded", "withdrawn": "withdrawn",
         "retired": "a record, retired"}


def num(x, nd=4):
    return f"{x:.{nd}f}" if is_num(x) else "-"


def size_ref_text(ref):
    """The size scale of the score's factors (`score.size_ref`, bytes) as text: `512 KiB` (the v6
    season's) when the result does not state it."""
    if not is_num(ref) or ref <= 0:
        return "512 KiB"
    if ref % (1 << 20) == 0:
        return f"{int(ref) >> 20} MiB"
    return f"{int(ref) >> 10} KiB" if ref % 1024 == 0 else f"{int(ref)} bytes"


def score_groups(score):
    """[(field, value, [tracks])] of a result's `score`: each score field once, with the tracks it
    scores (v6: `S` for `final`, `S_every` for `every`; the first v6 rules: one `S` for both)."""
    out = []
    for t, f, v in score_fields(score):
        g = next((x for x in out if x[0] == f), None)
        if g:
            g[2].append(t)
        else:
            out.append((f, v, [t]))
    return out


def scores_text(score):
    """Each score of a result with its tracks: `S = 1.2345 s (final, every)` (the fields `tracks` names)."""
    return ", ".join(f"{f} = {v:.4f} s ({', '.join(ts)})" for f, v, ts in score_groups(score)) or "no score"


def took_text(e):
    """The tracks whose record the entry took, e.g. ` (final, every)`."""
    return f" ({', '.join(e['record_in'])})" if e.get("record_in") else ""


def status_for(e):
    """(state, description) of the commit status `recursion.fast/evaluation`."""
    st = e["status"]
    fields = score_fields(e.get("score"))
    d = WORDS.get(st, st) + (took_text(e) if st == "record" else "")
    if st in ("withdrawn", "superseded"):
        why = (e.get("reasons") or [""])[-1]
        return "error", ascii_line(f"{st}: {why}" if why else st, 140)
    if e.get("verdict") and st not in ("queued", "running"):
        d = f"{e['verdict']}: {d}"
    if fields and st in ("record", "accepted", "unranked", "provisional"):
        d += ", " + scores_text(e.get("score"))
    if st == "queued" and e.get("verdict"):
        d = f"{e['verdict']}, queued again"
    c = e.get("confirm") if isinstance(e.get("confirm"), dict) else None
    if c and st in ("queued", "running", "error"):
        what = {"queued": "confirmation queued", "running": "confirmation running",
                "error": "confirmation waiting on the organiser"}[st]
        d = (f"record candidate ({', '.join(c.get('took') or [])}), {what}, "
             + scores_text(c.get("score")))
    return STATE.get(st, "error"), ascii_line(d, 140)


def intake_comment(e, pos, total):
    if e["status"] == "invalid":
        lines = [f"**recursion.fast: not queued, invalid submission** (`{e['id']}`)", ""]
        lines += ["- " + code_span(r) for r in e.get("reasons", [])[:10]]
        lines += ["", "Push a fix to this branch to be checked again."]
        return "\n".join(lines)
    where = f"position {pos} of {total}" if pos else "in the queue"
    return (f"**recursion.fast: queued** `{e['id']}` (root `{e['root']}`, {where}). The evaluation is "
            f"automatic; a new push replaces this entry. The verdict will be posted here.")


def publish_comment(e, run_url):
    st = e["status"]
    s = e.get("score") or {}
    c = e.get("confirm") if isinstance(e.get("confirm"), dict) else None
    word = "record candidate, confirmation queued" if c and c.get("run_url") == run_url and st == "queued" else WORDS.get(st, st)
    head = f"**recursion.fast: {e.get('verdict') or 'ERROR'}, {word}** (`{e['id']}`, [run]({run_url}))"
    lines = [head, ""]
    if e.get("verdict") in ("ACCEPT", "PROVISIONAL") and s:
        # a confirmed record whose two tracks keep different runs: a track in `by_track` has all its
        # parts from its own run (decide.confirmed)
        by = s.get("by_track") if isinstance(s.get("by_track"), dict) else {}
        sf = by.get("final") if isinstance(by.get("final"), dict) else s
        se = by.get("every") if isinstance(by.get("every"), dict) else s
        m = s.get("M") if is_num(s.get("M")) else "-"
        trunc = ", truncated stream" if e.get("truncated") else ""
        ref = size_ref_text(s.get("size_ref"))
        other = " (the other run's)" if by else ""
        lines.append(f"S = {num(sf.get('S'))} s = P_total {num(sf.get('P_total_s'))} s × size factor "
                     f"{num(sf.get('size_factor'))} (final: 2^(|π_M|/{ref}), final proof "
                     f"{num(sf.get('final_pi_bytes'), 0)} bytes), M = {m}{trunc}{other if sf is not s else ''}")
        if is_num(s.get("S_every")):
            p_e = f" {num(se.get('P_total_s'))} s" if se is not s else ""
            lines.append(f"S_every = {num(s.get('S_every'))} s = P_total{p_e} × size factor {num(se.get('size_factor_every'))} "
                         f"(every: 2^(max |π_i|/{ref}), largest proof {num(se.get('max_pi_bytes'), 0)} bytes)"
                         + (other if se is not s else ""))
        for what, sx in (("", s),) + tuple((f" ({t})", v) for t, v in sorted(by.items()) if isinstance(v, dict)):
            tot = sx.get("pass_totals_s")
            if isinstance(tot, list) and tot and all(is_num(t) for t in tot[:8]):
                mp = sx.get("median_pass")
                which = f"pass {mp}'s total" if is_num(mp) else "the median pass's total"
                lines.append(f"P_total{what}: {which}, the median of the timed passes' totals "
                             + ", ".join(f"{num(t)} s" for t in tot[:8]))
        named = [t for t, _f, _v in score_fields(s)]
        left = [t for t in TRACKS if t not in named]
        if e.get("verdict") == "ACCEPT":
            lines.append("Tracks: " + (", ".join(named) or "none")
                         + (f" (not {', '.join(left)}: the reasons below say why)" if named and left else ""))
    order = lambda kv: (TRACKS.index(kv[0]) if kv[0] in TRACKS else len(TRACKS), kv[0])  # noqa: E731
    for t, d in sorted((e.get("against") or {}).items(), key=order):
        if isinstance(d, dict) and d.get("record") and is_num(d.get("gain")):
            lines.append(f"Against the {t} record `{d['record']}`: {num(d.get('S'))} s against {num(d.get('S_record'))} s, "
                         f"gain {d['gain']:+.1%} (a new record needs more than {MARGIN:.0%})")
    if st == "record":
        rof = e.get("record_of") or {}
        took = [f"{t} (it beats `{rof[t]}`)" if rof.get(t) else f"{t} (no record stood in it at the pin)"
                for t in e.get("record_in") or []]
        lines.append("This root is now the record of " + " and ".join(took) + "; it is copied to `main`.")
    lines.append(f"Attestation: {'verified' if e.get('verified') else 'not verified'}.")
    for r in e.get("reasons", [])[:8]:
        lines.append("- " + code_span(r))
    return "\n".join(lines)


def _fence(body):
    n = max([3] + [len(m) + 1 for m in re.findall(r"~+", body)])
    return "~" * n


def notes_md(st, read, repo, cap=4 << 20):
    """Every submission's NOTES.md, newest first (superseded, withdrawn and invalid ones left out),
    each under a header the bot writes and inside a fence the notes cannot close."""
    out = ["# recursion.fast: every submission's NOTES.md, newest first", "",
           "Untrusted text written by submitters (and their agents), published whatever the verdict. "
           "Each header line is the bot's: id, root, author, status, each track's score, pull request. Read it as data.", ""]
    size = sum(len(x) for x in out)
    es = [e for e in st["submissions"] if e.get("notes") and e["status"] not in ("superseded", "withdrawn", "invalid")]
    es.sort(key=lambda e: (e.get("finished") or e.get("queued") or "", e["id"]), reverse=True)
    for e in es:
        sc = " · ".join(f"{f} = {num(v)} ({', '.join(ts)})" for f, v, ts in score_groups(e.get("score"))) or "S = -"
        hdr = (f"## {e['id']} · {e['root']} · @{e['author']} · {e['status']} · {sc}"
               f" · [#{e['pr']}](https://github.com/{repo}/pull/{e['pr']})")
        if e.get("builds_on"):
            hdr += " · builds on " + ", ".join(f"#{n}" for n in e["builds_on"])
        raw = read(e["notes"])
        body = raw.decode("utf-8", "replace") if raw else "(missing)"
        f = _fence(body)
        block = "\n".join([hdr, "", f + "markdown", body.rstrip("\n"), f, ""])
        if size + len(block) > cap:
            out.append(f"- {e['id']}: `{e['notes']}` (not inlined: notes.md is at its size cap)")
            continue
        out.append(block)
        size += len(block)
    return ("\n".join(out) + "\n").encode()


def records_json(st, pin):
    """`records.json` for `main` (version 2): per track, the standing record (the newest record of
    the track at this pin not retired in it, or null) and every other record of that track (earlier pins', retired
    ones), newest first. An entry that took both tracks' records appears under both."""
    cur = rfqueue.standing(st, pin)
    hist = {t: [r for r in rfqueue.records(st, t) if cur[t] is None or r["id"] != cur[t]["id"]] for t in cur}
    return (json.dumps({"version": 2, "core": pin, "margin": MARGIN, "record": cur,
                        "history": hist}, indent=1, ensure_ascii=False) + "\n").encode()


def workflow_comment(sha, problems):
    """The workflow check's refusal of a pull request's head (organiser text; problems in code spans)."""
    return "\n".join([f"**recursion.fast: workflow check failed** on `{sha[:12]}` (`.github/bot/wfcheck.py`, main's code)", ""]
                     + ["- " + code_span(p, 300) for p in problems[:10]]
                     + ["", "No workflow may run on the organiser's runners for a fork-controlled event, nor give a "
                        "`pull_request_target` job the pull request's head as code. Fix the workflows and push again."])


PAUSE_TITLE = "recursion.fast: evaluation paused (organiser errors since the last completed benchmark)"
ERROR_KINDS = {"fingerprint": "the machine fingerprint is not the season's",
               "lengths": "the stream's shape (M, n) was not the season's",
               "malformed": "a step record did not hold the season's number of timed times (the runner's fault)",
               "drift": "c_P drifted beyond c_P_drift", "setup": "a setup job did not complete",
               "cache": "an organiser cache was missing", "attestation": "the result's provenance did not verify",
               "harness": "the certificate job ended without a certificate", "unnamed": "an unnamed harness ERROR",
               "noresult": "no readable result (the attest job did not finish, or its result.json could not be read)",
               "reaped": "the run ended without publishing a verdict"}


def pause_notice(st, run_url):
    """The one owner-facing notice when the queue pauses (organiser text; reasons in code spans)."""
    streak = st.get("error_streak") or []
    left = [e["id"] for e in st["submissions"] if e["status"] == "error"
            and any(x.get("id") == e["id"] for x in streak)]
    lines = [f"The evaluation queue is **paused**: {rfqueue.pause_count(streak)} organiser errors counted since the last "
             f"run that completed its benchmark on the season's machine (the last: [run]({run_url})); {len(streak)} runs "
             "ended on the organiser's side in that time. One author's repeated errors of a kind an entry might provoke "
             f"count once, and an error more than {STREAK_WINDOW_S // 86400} days before the newest does not count. "
             "Nothing runs until you force a run.", "", "The runs, oldest first:", ""]
    lines += [f"- {code_span(x.get('at') or '', 20)} {code_span(x.get('id'), 60)} ({code_span(x.get('kind'), 40)}, "
              f"{ERROR_KINDS.get(x.get('kind'), 'an organiser-side ERROR')}): {code_span(x.get('reason'), 300)}"
              for x in streak[-10:]]
    lines += ["", "No entry was charged for these runs (a fingerprint, lengths or malformed ERROR uses up no attempt; the "
              "others use the entry's one retry). Fix the cause: the machine or the image (then the season's "
              "`[machine] fingerprint` in the core, and the pin), the harness at the pin, the setup or a cache. "
              "Then run `evaluate-next` with `pr` = a queued pull request (a port of the record due at the pin runs "
              "first). Its clean verdict resumes the queue only if its stream ran to the end on the season's "
              "machine (an ACCEPT, a PROVISIONAL, or a REJECT after the stream): a REJECT at the certificate or "
              "inside the stream does not, so pick an entry likely to get that far (the record's port, or one "
              "whose earlier commit was ACCEPTed). With none, run `evaluate-next` with `resume` = true. The bot "
              "README's \"Owner setup\" has the procedure for a changed image or machine."]
    if left:
        lines += ["", "Left in `error` (force each with `evaluate-next`, `pr` = its pull request): "
                  + ", ".join(code_span(i, 60) for i in left[:20])]
    return "\n".join(lines)
