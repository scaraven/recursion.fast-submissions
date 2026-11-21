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

An entry may take the records of several tracks at once. A prover binary that an earlier record of
any track already had never takes a record again (a resubmitted copy).

**Confirmation** (AGENTS.md §10). A result that would take a record (`decide` says `record`) is not
crowned at once, a port of a record to a new pin excepted: the same commit is evaluated once more at
the same pin (`candidate`, then `confirmed`). It takes the record of a track only if the
confirmation run too is a comparable, attested ACCEPT that takes that track by the rule above, and
the score it keeps is the worse (larger) of the two runs'. So one lucky run (a re-rolled NOTES, a
one-byte `.s` change) is not enough: the margin must hold twice."""
from common import (LEGACY_TRACKS, MARGIN, MAX_ATTEMPTS, ORGANISER_ERRORS, PAUSING_ERRORS, SHA_RE, TRACK_RE, TRACKS, VERDICTS,
                    clean, clean_reasons, is_num, track_scores)


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


def clean_score(raw):
    """A result's `score`, cleaned (`clean_value`, which keeps at most 48 keys), with `tracks` and the
    score fields it names (and the sum's `S`) copied from the raw object explicitly, so that no cap on
    the number of keys, and no order of them, can drop a track."""
    if not isinstance(raw, dict):
        return None
    out = clean_value(raw)
    names = raw.get("tracks")
    if isinstance(names, dict):
        names = {k: v for k, v in list(names.items())[:8] if isinstance(k, str) and TRACK_RE.match(k)
                 and isinstance(v, str) and v != "tracks" and clean(v, 40) == v}
        out["tracks"] = names
    fields = list(names.values()) if isinstance(names, dict) else []
    for f in fields + list(LEGACY_TRACKS.values()):
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
    if d["beats"]:
        return True, f"{track}: {S:.4f} s beats the record {rid} ({s_rec:.4f} s) by {d['gain']:.1%}", d
    return False, (f"{track}: {S:.4f} s against the record {rid}'s {s_rec:.4f} s ({d['gain']:+.1%}; a record "
                   f"needs more than {margin:.0%})"), d


def decide(result, verification, pin, records, attempts, record_provers=(), margin=MARGIN, tracks=None):
    """The fields an evaluation sets on its entry, with `requeue` (evaluate it once more) and
    `organiser_side` (the run ended on the organiser's side, not in a clean verdict) and
    `benchmarked` (the result records a stream on the season's machine: the run got past every
    benchmark-side check, so its clean verdict shows the machine and the harness work).

    result: the parsed result.json or None; verification: {"attested": bool, "record_ok": bool,
    "reason": str}; records: {track: the standing record's entry at this pin} (a track with none
    standing is absent or None); attempts: this entry's evaluations so far in this round, this one
    included; record_provers: {prover_sha256: id} of every record of every track (but this commit's
    own); tracks: the tracks this entry is a candidate in (a port: those whose record it carries to
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
            what = "machine fingerprint" if out["organiser_error"] == "fingerprint" else "the season's stream shape"
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
    elif isinstance(result.get("prover_sha256"), str) and result["prover_sha256"] in record_provers:
        status = "accepted"
        extra.append(f"the same prover binary as the record {record_provers[result['prover_sha256']]}: never a new record")
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


def cache_retry(result, entry):
    """True if a REJECT used the record build cache (its certificate restored modules from it) and this entry was not yet evaluated without it: it is queued once more with
    `record_cache: false`, so a sabotaged cache cannot fail a candidate. An ERROR's retry runs
    without the cache anyway (flows.publish)."""
    if not isinstance(result, dict) or result.get("verdict") != "REJECT" or entry.get("record_cache") is False:
        return False

    def restored(r):
        c = (r or {}).get("certificate") if isinstance(r, dict) else None
        rc = (c or {}).get("record_cache") if isinstance(c, dict) else None
        return isinstance(rc, dict) and bool(rc.get("restored"))
    legacy = result.get("record_cache")
    return restored(result) or (isinstance(legacy, dict) and bool(legacy.get("reused")))


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
    fields to set: `status` (`record` iff some track is taken by both runs, else `accepted`), `took`,
    `score` (the worse run's: the larger score in the first track taken), `against`, `record_of`
    (that run's comparisons) and the `reasons` line that says what the confirmation did."""
    if d2["requeue"] or d2["status"] in ("queued", "error"):
        return None
    took = [t for t in first["took"] if t in d2["took"]]
    s1, s2 = track_scores(first["score"]), track_scores(d2["score"])
    lead = first["took"][0]
    ok2 = d2["status"] in ("record", "accepted") and lead in s2
    second_worse = ok2 and s2[lead] >= s1.get(lead, 0)
    w = {"score": d2["score"], "against": d2["against"], "record_of": d2["record_of"]} if second_worse else first
    both = (f"{lead}: S = {s1.get(lead, 0):.4f} s, then {s2[lead]:.4f} s in the confirmation" if lead in s2
            else f"{lead}: S = {s1.get(lead, 0):.4f} s; the confirmation has no score in it")
    if took:
        why = (f"confirmed: the confirmation run also takes the record of {', '.join(took)} ({both}); "
               f"the record keeps the worse score")
        lost = [t for t in first["took"] if t not in took]
        if lost:
            why += f"; not confirmed in {', '.join(lost)}"
        return {"status": "record", "took": took, "score": w["score"], "against": w["against"],
                "record_of": {t: (w["record_of"] or {}).get(t) for t in (w["record_of"] or {})}, "reasons": [why]}
    what = (f"its verdict is {d2['verdict']} ({d2['status']})" if d2["status"] not in ("record", "accepted")
            else "it does not beat the standing record by the margin")
    return {"status": "accepted", "took": [], "score": w["score"] if ok2 else first["score"],
            "against": d2["against"] if ok2 else first["against"],
            "record_of": {t: None for t in (first["record_of"] or {})},
            "reasons": [f"not a record: the confirmation run of this record candidate did not confirm it: {what} ({both})"]}
