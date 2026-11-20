"""The status of an evaluated entry and the record rule (TRUSTED; pure).

A result can become a record only if its verdict is ACCEPT, it is comparable (the stream not
truncated; a run off the season's machine is the core's ERROR, never an ACCEPT), its attestation verifies (the core's signer workflow
at the pin, on the organiser's self-hosted runner, bound to this run), the core's
`harness/verify-record.sh` accepts it, and `harness_commit` is the pin. Then, once per track `t`
the result scores (`common.score_fields`; AGENTS.md §10):

- with no record of `t` standing at the pin, it is the record of `t`;
- with a standing record of `t`, it is the record of `t` iff `S_t < (1 - MARGIN) * S_t,record`,
  `S_t,record` that record's own score in `t` at the pin (both measured on the same machine, as
  comparability requires).

An entry may take the records of several tracks at once. A prover binary (or the same prover
sources) that an earlier record of any track already had never takes a record again (a resubmitted
copy), unless the record is another author's that was queued after this entry's author first showed
that prover: the earliest-queued owner of a prover wins, and such a record is set aside when this
entry is compared (rfqueue.prover_owner).

**Confirmation** (AGENTS.md §10). A result that would take a record (`decide` says `record`) is not
crowned at once, a port of a record to a new pin excepted: the same commit is evaluated once more at
the same pin (`candidate`, then `confirmed`). It takes the record of a track only if the
confirmation run too is a comparable, attested ACCEPT that takes that track by the rule above, and
the score it keeps is the worse (larger) of the two runs'. Challengers are then compared with that
worse score. This halves the gain a lucky first run alone can give, but it does not make the margin
hold twice in effect: a near-copy of the record (the same speed) is a new record in about 15.9 % of
attempts at a run-to-run spread σ of 1.75 %, 4.1 % at σ = 1 %, 0.03 % at σ = 0.5 % (the heavy
review's Monte Carlo; comparing with the mean of the record's two runs instead would give 5.5 % at
σ = 1.75 %: the owner's choice, .github/bot/README.md). The defences against noise mining are the
copy rules (rfqueue.duplicate_of, rfqueue.prover_owner) and the owner's `retire`."""
from common import (LEGACY_TRACKS, MARGIN, MAX_ATTEMPTS, ORGANISER_ERRORS, PAUSING_ERRORS, SHA_RE, TRACK_RE, TRACKS, VERDICTS,
                    clean, clean_reasons, is_num, score_fields, track_scores, unit_text)


def clean_value(v, depth=0):
    if is_num(v) or isinstance(v, bool) or v is None:
        return v
    if isinstance(v, str):
        return clean(v, 200)
    if depth >= 3:
        return None
    if isinstance(v, list):
        return [clean_value(x, depth + 1) for x in v[:16]]
    if isinstance(v, dict):
        return {clean(k, 40): clean_value(x, depth + 1) for k, x in list(v.items())[:48]}
    return None


SIZE_RULE_FIELDS = ("size_ref", "size_factor", "final_pi_bytes")


def clean_score(raw):
    """A result's `score`, cleaned (`clean_value`, which keeps at most 48 keys), with `tracks` and the
    score fields it names (and the sum's `S`) copied from the raw object explicitly, so that no cap on
    the number of keys, and no order of them, can drop a track; so are the fields that say how the
    size factor is computed (this season's is the final proof's size; an earlier v6 season's names
    `size_ref`), which set the unit and the factor the bot and the site describe (common.product_rule)."""
    if not isinstance(raw, dict):
        return None
    out = clean_value(raw)
    names = raw.get("tracks")
    if isinstance(names, dict):
        names = {k: v for k, v in list(names.items())[:8] if isinstance(k, str) and TRACK_RE.match(k)
                 and isinstance(v, str) and v != "tracks" and clean(v, 40) == v}
        out["tracks"] = names
    fields = list(names.values()) if isinstance(names, dict) else []
    for f in fields + list(LEGACY_TRACKS.values()) + list(SIZE_RULE_FIELDS):
        if is_num(raw.get(f)):
            out[f] = raw[f]
    return out


def against(S, record, track, margin=MARGIN):
    """(beats, reason, comparison) of a comparable, attested ACCEPT with score `S` in `track` against
    that track's standing `record` (AGENTS.md §10): beats iff `S < (1 - margin) * S_record`, `S_record`
    the record's own score in the track."""
    rid, s_rec = record["id"], track_scores(record.get("score")).get(track)
    if s_rec is None:
        return False, f"{track}: the record {rid} has no positive score in this track: no comparison", None
    d = {"record": rid, "S": S, "S_record": s_rec, "gain": 1 - S / s_rec, "beats": S < (1 - margin) * s_rec}
    u = unit_text(record.get("score"), ascii=True)     # the record's, at the pin: the entry's too
    if d["beats"]:
        return True, f"{track}: {S:.4f} {u} beats the record {rid} ({s_rec:.4f} {u}) by {d['gain']:.1%}", d
    return False, (f"{track}: {S:.4f} {u} against the record {rid}'s {s_rec:.4f} {u} ({d['gain']:+.1%}; a record "
                   f"needs more than {margin:.0%})"), d


def result_prover_keys(result):
    """{(key, hash)} of a result's prover: its binary's `prover_sha256` and its sources' hash
    (`entry.prover_sources_sha256`), each 64 ASCII letters or digits, as the entry stores them
    (rfqueue.prover_keys)."""
    ent = result.get("entry") if isinstance(result, dict) and isinstance(result.get("entry"), dict) else {}
    pairs = (("prover_sha256", (result or {}).get("prover_sha256")), ("prover_sources_sha256", ent.get("prover_sources_sha256")))
    return {(k, v) for k, v in pairs if isinstance(v, str) and len(v) == 64 and v.isascii() and v.isalnum()}


def barred_by(result, record_provers):
    """The id of the record whose prover binary (or sources) this result has, or None."""
    return next((record_provers[v] for _k, v in sorted(result_prover_keys(result)) if v in record_provers), None)


def decide(result, verification, pin, records, attempts, record_provers=(), margin=MARGIN, tracks=None):
    """The fields an evaluation sets on its entry, with `requeue` (evaluate it once more) and
    `organiser_side` (the run ended on the organiser's side, not in a clean verdict) and
    `benchmarked` (the result records a stream on the season's machine: the run got past every
    benchmark-side check, so its clean verdict shows the machine and the harness work).

    result: the parsed result.json or None; verification: {"attested": bool, "record_ok": bool,
    "reason": str}; records: {track: the standing record's entry at this pin} (a track with none
    standing is absent or None); attempts: this entry's evaluations so far in this round, this one
    included; record_provers: {hash: id}, the prover binary and sources hashes of the records that
    bar this entry (rfqueue.prover_owner: of another commit, and its own author's or queued first);
    tracks: the tracks this entry is a candidate in (a port: those whose record it carries to
    the pin), None for every track.

    `took` lists the tracks whose record it takes (status `record` iff it is not empty);
    `record_of` and `against` give, per track, the record it beat and the comparison with it."""
    benchmarked = (isinstance(result, dict) and isinstance(result.get("stream"), dict)
                   and isinstance(result.get("machine"), dict) and result["machine"].get("matches") is True)
    if not isinstance(result, dict):
        result = {"verdict": "ERROR", "reasons": ["harness error: the evaluation produced no readable result "
                                                  "(no `result` artifact: a job failed before the attest job)"]}
    verdict = result.get("verdict") if result.get("verdict") in VERDICTS else "ERROR"
    score = clean_score(result.get("score"))
    scores = track_scores(score)
    every = list(TRACKS) + [t for t in scores if t not in TRACKS]
    hc = result.get("harness_commit") if isinstance(result.get("harness_commit"), str) and SHA_RE.match(result["harness_commit"]) else None
    out = {"verdict": verdict, "score": score, "comparable": result.get("comparable") is True,
           "truncated": result.get("truncated") is True, "harness_commit": hc,
           "verified": bool(verification.get("attested")), "took": [], "record_of": {t: None for t in every},
           "against": {t: None for t in every}, "requeue": False,
           "organiser_error": None, "organiser_side": False, "error_reason": None,
           "benchmarked": benchmarked}
    if out["verified"] and verdict == "ERROR" and result.get("organiser_error") in ORGANISER_ERRORS:
        out["organiser_error"] = result["organiser_error"]      # named by the core (attested)
    elif not out["verified"]:
        out["organiser_error"] = "attestation"                  # the provenance failed: the organiser's side
    reasons = clean_reasons(result.get("reasons"))
    extra = []
    # an ACCEPT scored in some tracks only (v6: `final` but not `every`): the core's reason, kept.
    # `tracks_reason` is {track: why} (the core's form) or one string for every missing track
    raw_score = result.get("score") if isinstance(result.get("score"), dict) else {}
    why = raw_score.get("tracks_reason") or result.get("tracks_reason")
    if verdict == "ACCEPT" and scores:
        for t in (t for t in TRACKS if t not in scores):
            w = why.get(t) if isinstance(why, dict) else why
            if isinstance(w, str) and w.strip():
                extra.append(f"not scored in {t}: {clean(w, 240)}")

    def error(why=None):
        out["organiser_side"] = True                    # not a clean verdict: it joins the error streak
        out["error_reason"] = why or (reasons[0] if reasons else None)
        if why:
            extra.append(why)
        if out["organiser_error"] in PAUSING_ERRORS:    # the organiser's, not the entry's: never uses up the retry
            out["requeue"] = True
            what = {"fingerprint": "machine fingerprint", "lengths": "the season's stream shape",
                    "malformed": "a malformed stream record"}.get(out["organiser_error"], out["organiser_error"])
            extra.append(f"organiser ERROR ({what}): queued again; this run does not count as an attempt")
            return "queued"
        if attempts < MAX_ATTEMPTS:
            out["requeue"] = True
            extra.append(f"organiser-side ERROR; queued again (attempt {attempts} of {MAX_ATTEMPTS})")
            return "queued"
        return "error"

    if not out["verified"]:
        # any result whose provenance fails is the organiser's problem, whatever it says
        status = error("attestation not verified: " + clean(verification.get("reason") or "no attestation", 240))
    elif verdict == "ERROR":
        status = error()
    elif verdict == "REJECT":
        status = "rejected"
    elif verdict == "PROVISIONAL":
        status = "provisional"
    elif hc != pin:
        status = error(f"the result's harness_commit {hc} is not the pin {pin}")
    elif not out["comparable"]:
        status = "unranked"
        extra.append("ACCEPT, not comparable (" + ("truncated stream" if out["truncated"]
                                                    else "the job plan") + "): not ranked")
    elif not verification.get("record_ok"):
        status = error("harness/verify-record.sh refused the ACCEPT: " + clean(verification.get("reason"), 240))
    elif not scores:
        status = "unranked"
        extra.append("ACCEPT without a positive score in any track: not ranked")
    elif barred_by(result, record_provers):
        status = "accepted"
        extra.append(f"the same prover binary as the record {barred_by(result, record_provers)}: never a new record")
    else:
        for t, S in scores.items():
            rec = (records or {}).get(t)
            if tracks is not None and t not in tracks:
                extra.append(f"{t}: a port is a candidate only in the tracks whose record it carries ({', '.join(tracks)})")
            elif rec is None:
                out["took"].append(t)
                extra.append(f"{t}: no record stood in this track at the pin")
            else:
                beats, why, out["against"][t] = against(S, rec, t, margin)
                extra.append(why)
                if beats:
                    out["took"].append(t)
                    out["record_of"][t] = rec["id"]
        status = "record" if out["took"] else "accepted"
    out["status"] = status
    out["reasons"] = reasons[:max(0, 20 - len(extra))] + extra[:20]
    return out


# The stages at which a REJECT can have been caused by the record build cache (the core's top-level
# `reject_stage`): a restored module can make the certificate fail, and a restored module's `.c` is
# what the badge is compiled from, so a forged one shows as a failed check. The prover is built from
# the entry's own `.s`, never from the cache, so a REJECT of the prover's build or setup, a failed
# request, a timed pass's mismatch or the stream cap is final. A `check` REJECT is retried, but the
# retry can overturn it only if the clean rebuild's badge differs from the first run's
# (`cache_check_stands`): an entry that fails a check on purpose (a bad output, made in the untimed
# service run when the prover senses a slow machine) gets its own REJECT back, never a second draw.
CACHE_STAGES = ("certificate", "check")


def is_new_rules(result):
    """True if a result comes from a core of the committed-leaf rules or later, which records
    `reject_stage` on every REJECT: its stream record names the leaf data's expansion
    (`stream.leaf_data`), or its score has the median pass (`pass_totals_s`) or `S_every`."""
    st, sc = result.get("stream"), result.get("score")
    if isinstance(st, dict) and "leaf_data" in st:
        return True
    return isinstance(sc, dict) and ("pass_totals_s" in sc or "S_every" in sc
                                     or (isinstance(sc.get("tracks"), dict) and sc["tracks"].get("every") == "S_every"))


def reject_stage(result):
    """Where a REJECT was rejected: the core's `reject_stage` when it names one; else `certificate`
    if the certificate was rejected; else None (unknown, so final) for a result of a core that
    records the stage (it is present but empty, or `is_new_rules`); else `legacy` (a result of an
    earlier core, which records no stage)."""
    rs = result.get("reject_stage")
    if isinstance(rs, str) and rs:
        return rs
    c = result.get("certificate")
    if isinstance(c, dict) and c.get("status") == "reject":
        return "certificate"
    return None if "reject_stage" in result or is_new_rules(result) else "legacy"


def badge_sha(result):
    """The attested hashes of the badge's files (`certificate.badge_sha256`, {name: sha256}), or None."""
    c = result.get("certificate") if isinstance(result, dict) else None
    b = c.get("badge_sha256") if isinstance(c, dict) else None
    ok = (isinstance(b, dict) and 0 < len(b) <= 8 and all(isinstance(k, str) and isinstance(v, str) and len(v) == 64
                                                          for k, v in b.items()))
    return {k[:64]: v for k, v in b.items()} if ok else None


def cache_retry(result, entry, verified):
    """True if a verified REJECT used the record build cache (its certificate restored modules from
    it), the cache can have caused it (`reject_stage`: `certificate` or `check`, CACHE_STAGES; a
    result of an earlier core, which records no stage, is retried whatever its stage, as before; a
    result of this rules' core without a stage is not), and this entry was not yet evaluated without
    it: it is queued once more with `record_cache: false`, so a sabotaged cache cannot fail a
    candidate. An ERROR's retry runs without the cache anyway (flows.publish)."""
    if (not verified or not isinstance(result, dict) or result.get("verdict") != "REJECT"
            or entry.get("record_cache") is False):
        return False
    if reject_stage(result) not in CACHE_STAGES + ("legacy",):
        return False

    def restored(r):
        c = (r or {}).get("certificate") if isinstance(r, dict) else None
        rc = (c or {}).get("record_cache") if isinstance(c, dict) else None
        return isinstance(rc, dict) and bool(rc.get("restored"))
    legacy = result.get("record_cache")
    return restored(result) or (isinstance(legacy, dict) and bool(legacy.get("reused")))


def cache_check(result, run_url, reasons):
    """What a `check` REJECT retried without the record build cache keeps for its retry (`cache_check` on
    the entry), or None for any other retried stage: the first run, its reasons and its badge."""
    if reject_stage(result) != "check":
        return None
    return {"run_url": run_url, "badge_sha256": badge_sha(result), "reasons": list(reasons)[:20]}


def cache_check_stands(pending, result):
    """True if the first run's `check` REJECT stands after the retry without the cache: the clean
    rebuild's badge is byte-identical to the first run's, so the cache cannot have caused the failed
    check (an unknown badge on either side: the retry decides, as before)."""
    a, b = (pending or {}).get("badge_sha256"), badge_sha(result)
    return bool(a) and a == b


def build_manifest_sha(result):
    """The attested sha256 of the entry build's manifest.json (certificate.entry_build first, then a
    top-level entry_build), or None."""
    if not isinstance(result, dict):
        return None
    for holder in (result.get("certificate"), result):
        eb = holder.get("entry_build") if isinstance(holder, dict) else None
        h = eb.get("manifest_sha256") if isinstance(eb, dict) else None
        if isinstance(h, str) and len(h) == 64 and all(c in "0123456789abcdef" for c in h):
            return h
    return None


def candidate(d, pin, run_url, result_path=None):
    """The pending confirmation of a first run whose decision `d` takes a record (`d["took"]`): what
    the confirmation run is compared with (`confirmed`). Stored on the entry as `confirm`."""
    return {"pin": pin, "run_url": run_url, "result": result_path, "took": list(d["took"]),
            "score": d["score"], "against": d["against"], "record_of": d["record_of"]}


def confirmed(first, d2):
    """Combines the confirmation run's decision `d2` (`decide` at the same pin, against the same
    standing records) with the pending `first` run (`candidate`). Returns None if `d2` ends on the
    organiser's side or is queued again (the confirmation stays pending, retried as any run), else the
    fields to set: `status`, `took`, `score`, `against`, `record_of`, the `reasons` line that says
    what the confirmation did, and `score_run` (`first` or `confirmation`: the run whose result the
    entry's score object is, so the entry's run link and result JSON name it).

    `status` is `record` iff some track is taken by both runs; else the confirmation's own status if
    it is not an ACCEPT that ranks (`rejected`, `provisional`, `unranked`: the entry's status follows
    the confirmation's verdict), else `accepted`.

    The record keeps the worse run **per track**: in each track taken, the score field `tracks` names
    holds the larger of the two runs' scores, and `against`/`record_of` are that run's comparison in
    that track (`S` and `S_every` can order the two runs differently). The score object is the run
    that is worse in the first track taken, whole; a track taken whose worse run is the other one
    has all its fields from that run in `score.by_track[track]` (P_total, the passes, its size
    factor and proof size), so every part shown with a track's score is of the run that gave it."""
    if d2["requeue"] or d2["status"] in ("queued", "error"):
        return None
    took = [t for t in first["took"] if t in d2["took"]]
    s1, s2 = track_scores(first["score"]), track_scores(d2["score"])
    lead = first["took"][0]
    ok2 = d2["status"] in ("record", "accepted") and lead in s2
    run1 = {"score": first["score"], "against": first["against"], "record_of": first["record_of"], "run": "first"}
    run2 = {"score": d2["score"], "against": d2["against"], "record_of": d2["record_of"], "run": "confirmation"}

    def worse(t):
        return run2 if t in s2 and s2[t] >= s1.get(t, 0) else run1
    w = worse(lead) if ok2 else run1
    u = unit_text(first["score"], ascii=True)
    both = (f"{lead}: S = {s1.get(lead, 0):.4f} {u}, then {s2[lead]:.4f} {u} in the confirmation" if lead in s2
            else f"{lead}: S = {s1.get(lead, 0):.4f} {u}; the confirmation has no score in it")
    if took:
        score = {k: v for k, v in (w["score"] or {}).items() if k != "by_track"}
        names = dict(score.get("tracks") or {}) if isinstance(score.get("tracks"), dict) else None
        against, record_of = dict(w["against"] or {}), {t: None for t in (w["record_of"] or {})}
        by = {}
        for t in took:
            wt = worse(t)
            f = next((f for tt, f, _v in score_fields(wt["score"]) if tt == t), None)
            if f is not None:
                score[f] = track_scores(wt["score"])[t]
                if names is not None:
                    names[t] = f
            if wt is not w:
                by[t] = {k: v for k, v in (wt["score"] or {}).items() if k not in ("tracks", "by_track", "tracks_reason")}
            against[t] = (wt["against"] or {}).get(t)
            record_of[t] = (wt["record_of"] or {}).get(t)
        if names is not None:
            score["tracks"] = names
        if by:
            score["by_track"] = by
        per = "; ".join(f"{t}: {s1.get(t, 0):.4f} {u}, then {s2.get(t, 0):.4f} {u}" for t in took)
        why = (f"confirmed: the confirmation run also takes the record of {', '.join(took)} ({per}); "
               f"the record keeps the worse run in each track")
        lost = [t for t in first["took"] if t not in took]
        if lost:
            why += f"; not confirmed in {', '.join(lost)}"
        return {"status": "record", "took": took, "score": score, "against": against,
                "record_of": record_of, "reasons": [why], "score_run": w["run"]}
    none = {t: None for t in (first["record_of"] or {})}
    if d2["status"] not in ("record", "accepted"):
        # the confirmation is not an ACCEPT that ranks: the entry takes its verdict's status
        return {"status": d2["status"], "took": [], "score": d2["score"], "against": d2["against"], "record_of": none,
                "score_run": "confirmation",
                "reasons": [f"not a record: the confirmation run of this record candidate did not confirm it: its verdict "
                            f"is {d2['verdict']} ({d2['status']}), so this entry is {d2['status']} ({both})"]}
    return {"status": "accepted", "took": [], "score": w["score"], "against": w["against"], "record_of": none,
            "score_run": w["run"],
            "reasons": [f"not a record: the confirmation run of this record candidate did not confirm it: it does not "
                        f"beat the standing record by the margin ({both})"]}
