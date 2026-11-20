"""Constants and the sanitisers every module uses (TRUSTED; the bot of recursion.fast-submissions).

Every string that reaches `data`, a comment or a commit status from a pull request (its title, the
NOTES header, file names, the result's reasons) goes through `clean` or `code_span` first.
"""
import datetime
import re

CORE_REPO = "scaraven/recursion.fast"
SIGNER_WORKFLOW = "scaraven/recursion.fast/.github/workflows/evaluate.yml"
STATUS_CONTEXT = "recursion.fast/evaluation"
# The record rule (AGENTS.md §10), per track t: a comparable, attested ACCEPT at the pin is a new
# record of t iff S_t < (1 - MARGIN) * S_t,record, S_t,record the standing record's score in t at the pin.
# MARGIN is the owner's choice (2 %), not derived from the noise. For reference: σ, the relative
# run-to-run spread of S for one entry on the evaluation machine with a fixed stream, was
# measured at 1.75 % over 10 runs at the smoke shape (the core's harness/smoke.toml; mostly per-step
# process overhead) under the earlier rules, with one timed pass. The v6 rules take the median of
# three timed passes' totals over 16 steps; from one step's measured spread (about 0.9 %) that
# median varies by about 0.15 % [model], and the core estimates σ ≈ 0.2–0.5 % per evaluation
# [estimate], unmeasured at the season's shape. S and S_record are two independent runs, so two
# runs of one entry differ by about √2·σ (≈ 2.5 % at σ = 1.75 %), and a noise-proof single-run margin
# would be 3·√2·σ ≈ 7.4 % there; at σ ≈ 0.5 % the 2 % margin is about 3·√2·σ.
# The defences are elsewhere: a record candidate is confirmed by a second run of the same commit that
# must also beat the record, and the record keeps the worse run (decide.confirmed); measured by a
# Monte Carlo of that rule, a near-copy of the record (the same speed) is still crowned in about
# 15.9 % of attempts at σ = 1.75 %, 4.1 % at σ = 1 % and 0.03 % at σ = 0.5 % (comparing with the mean
# of the record's two runs would give 5.5 % at σ = 1.75 %: the owner's choice, README.md). A copy of
# an evaluated root or of its prover/ is invalid, a record's prover binary never takes the record
# again (rfqueue.prover_owner), and the owner retires a record won by noise (`retire`). The owner may
# change MARGIN between seasons (a stored state with another margin is rewritten at once,
# rfqueue.load; README.md, "Changing the margin", lists every place that states it).
MARGIN = 0.02
# The tracks (the core's AGENTS.md §7, §8): one evaluation, one score `S`, two eligibilities, each
# track with its own records. `final`: only the final proof is verified; `every`: every proof is.
# A result's `score.tracks` names, per track, the field of `score` that is its score
# ({"final": "S", "every": "S_every"}: `final` prices the final proof's size, `every` the largest
# proof's; `every` is absent when the entry is eligible for `final` only, and
# `tracks_reason` says why). A score without `tracks` (a result of an earlier season) has the sum of
# that season alone, `S` (LEGACY_TRACKS). The record rule runs once per track that the result names,
# with the one MARGIN. TRACKS is the order the bot lists them in, the tracks `record` always names
# and the only tracks whose records are ported to a new pin; a track a result names that is not here
# (an earlier season's `sum`, `product`) is decided the same way and kept in the history.
TRACKS = ("final", "every")
LEGACY_TRACKS = {"sum": "S"}
TRACK_RE = re.compile(r"[a-z][a-z0-9_]{0,15}\Z")
MAX_ATTEMPTS = 2          # an organiser-side ERROR is evaluated once more, then left for the owner
# Organiser errors the core names in a result (`organiser_error`), and `attestation`, which the bot
# gives a result whose provenance does not verify (nothing an entry runs can reach the attest job).
# `drift` is among them although c_P is sampled during the entry's stream: the sandbox leaves no
# entry process alive, so only a thermal effect could carry over (accepted and documented). These are
# the organiser's alone: a run that ends in one never counts against the author (it does not move
# the author back in the fair order). A `fingerprint` error (the machine is not the season's), a
# `lengths` error (the stream's shape, M and n, was not the season's: an organiser bug, the
# same at every retry at one pin) or a `malformed` error (a step record whose timed times are not
# the season's `timed_runs` numbers, so the score cannot be computed: the runner's fault, likewise
# the same at every retry) does not even use up the entry's retry; the others are retried once
# (MAX_ATTEMPTS). `attestation`: an unverified result (the bot's). `harness` (the certificate job
# ended without a certificate) is named but counts in the fair order as an unnamed ERROR does (from
# the entry's second), and so does a run with no result at all (flows.publish): an entry might
# provoke either.
UNCOUNTED_ERRORS = ("fingerprint", "lengths", "malformed", "drift", "setup", "cache", "attestation")
ORGANISER_ERRORS = UNCOUNTED_ERRORS + ("harness",)
PAUSING_ERRORS = ("fingerprint", "lengths", "malformed")     # a retry cannot clear them: re-queued in place without an attempt
# The pause (AGENTS.md §9): every run that ends on the organiser's side (any ERROR, named or not, a
# result whose provenance fails, no result at all, a run reaped after it died) joins the error
# streak. Only a clean verdict (a verified ACCEPT, PROVISIONAL or REJECT) whose stream ran on the
# season's machine clears it; a REJECT at the certificate or inside the stream never reached the
# benchmark-side checks and leaves it as it is. When PAUSE_AFTER errors of the streak count, the
# queue pauses and one issue is opened for the owner. An entry cannot cause an ENTRY_PROOF error
# (decided before any entry code runs, or by jobs that never fetch the entry; `malformed` is the
# runner's own record of the stream, which no entry writes; `attestation` here is a result that
# exists but whose provenance fails), so each one counts. The others (drift, measured
# during the entry's stream; harness, the certificate job, which builds the entry, ended without a
# certificate; no result at all; an unnamed ERROR; a reaped run) might be provoked by an entry, so
# they count once per author in the streak: no author can pause the queue alone, and an outage still
# pauses it at the second author's entry. An error more than STREAK_WINDOW_S before the streak's
# newest no longer counts, so unrelated errors weeks apart do not add up to a pause.
ENTRY_PROOF_ERRORS = ("fingerprint", "lengths", "malformed", "setup", "cache", "attestation")
PAUSE_AFTER = 2
STREAK_CAP = 32           # the streak's newest runs kept in the state
STREAK_WINDOW_S = 7 * 24 * 3600

ROOT_RE = re.compile(r"[a-z][a-z0-9-]{0,39}\Z")
SHA_RE = re.compile(r"[0-9a-f]{40}\Z")
ID_RE = re.compile(r"pr[1-9][0-9]{0,8}-[0-9a-f]{12}(?:-[0-9a-f]{8})?\Z")   # -<pin8>: a port to a new pin
LOGIN_RE = re.compile(r"[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})(?:\[bot\])?\Z")

QUEUED, RUNNING = "queued", "running"
FINAL = ("record", "retired", "accepted", "unranked", "provisional", "rejected", "error", "invalid",
         "superseded", "withdrawn")
STATUSES = (QUEUED, RUNNING) + FINAL
VERDICTS = ("ACCEPT", "PROVISIONAL", "REJECT", "ERROR")

# The entry caps: exactly the `[entry]` section of the core's harness/season.toml at the pin (the
# harness is authoritative; pin-core.sh warns when a new pin's values differ). A breach is invalid.
ENTRY_CAPS = {"files": 2048, "bytes": 512 << 20, "file_bytes": 128 << 20, "lean_files": 1024,
              "lean_bytes": 32 << 20, "prover_files": 256, "prover_bytes": 256 << 20, "claim_bytes": 64 << 10}
MAX_PR_FILES = 3000       # the pull-request files API lists at most 3000
MAX_TEXT_BYTES = 64 << 10   # NOTES.md, README.md (the bot's own cap)
MAX_HEADS_PER_PR = 50       # compact entries kept per pull request (older ones are dropped)
MAX_PATH = 512            # bytes of the whole path, `submissions/<root>/` included


def entry_id(pr, sha):
    """The id of one evaluated commit of one pull request: `pr<N>-<first 12 hex of the sha>`."""
    return f"pr{int(pr)}-{sha[:12]}"


def now_iso(clock=None):
    t = clock() if clock else datetime.datetime.now(datetime.timezone.utc)
    return t.strftime("%Y-%m-%dT%H:%M:%SZ")


def clean(s, cap):
    """Untrusted text as one printable line of at most `cap` characters (Unicode letters kept;
    control, format (bidi) and separator characters other than space become `?`)."""
    s = " ".join(str(s if s is not None else "").split())
    out = "".join(c if c.isprintable() else "?" for c in s)
    return out if len(out) <= cap else out[: max(cap - 1, 0)] + "…"


def ascii_line(s, cap):
    """Untrusted text as printable ASCII, at most `cap` characters, with no backtick."""
    s = " ".join(str(s if s is not None else "").split())
    out = "".join(c if 32 <= ord(c) < 127 else "?" for c in s).replace("`", "'")
    return out if len(out) <= cap else out[: max(cap - 3, 0)] + "..."


def code_span(s, cap=300):
    """Untrusted text for a comment: printable ASCII in a code span, so no markdown, link, HTML or
    @-mention in it is rendered."""
    return "`" + (ascii_line(s, cap) or " ") + "`"


def clean_reasons(rs, n=20, cap=300):
    if not isinstance(rs, list):
        rs = [rs] if rs else []
    return [clean(r, cap) for r in rs[:n]]


def is_num(x):
    return isinstance(x, (int, float)) and not isinstance(x, bool) and x == x and abs(x) != float("inf")


def score_fields(score):
    """[(track, field, value)] of a result's `score` object, in TRACKS order: the field
    `score.tracks[track]` names and its value, for each track whose score is a positive number (a
    score without `tracks`: an earlier season's sum, `S`, only). At most 8 tracks."""
    if not isinstance(score, dict):
        return []
    names = score.get("tracks") if isinstance(score.get("tracks"), dict) else LEGACY_TRACKS
    out = []
    for t, f in list(names.items())[:8]:
        v = score.get(f) if isinstance(f, str) and f != "tracks" else None
        if isinstance(t, str) and TRACK_RE.match(t) and is_num(v) and v > 0:
            out.append((t, f, v))
    return sorted(out, key=lambda x: (TRACKS.index(x[0]) if x[0] in TRACKS else len(TRACKS), x[0]))


def track_scores(score):
    """{track: the positive score in that track} of a result's `score` object (`score_fields`)."""
    return {t: v for t, _f, v in score_fields(score)}


# The score's size factor (the core's AGENTS.md §8): this season's is the priced proof's size in
# bytes itself, S = P_total · |π_M| in `final` and S_every = P_total · max_i |π_i| in `every`
# (`score.size_factor` = `final_pi_bytes`, `size_factor_every` = `max_pi_bytes`), so a score is in
# seconds times bytes. An earlier v6 season's was exponential, 2^(|π_M| / size_ref) (the core named
# `size_ref`), a score in seconds. The record rule compares scores of one pin only, so it never
# mixes the two.
def product_rule(score):
    """Whether a result's size factor is this season's (the proof size in bytes) rather than an
    earlier v6 season's exponential (`size_ref`): its `size_factor` equals its `final_pi_bytes`."""
    if not isinstance(score, dict) or "size_ref" in score:
        return False
    f, pi = score.get("size_factor"), score.get("final_pi_bytes")
    return is_num(f) and is_num(pi) and pi > 0 and abs(f - pi) <= 1e-9 * pi


def unit_text(score, ascii=False):
    """The unit of a result's scores: seconds times bytes at this season's rule (`s·B`, `s*B` in
    ASCII), seconds for an earlier season's (an exponential factor, or none)."""
    return ("s*B" if ascii else "s·B") if product_rule(score) else "s"
