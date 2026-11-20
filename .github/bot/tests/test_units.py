import json
import re
import subprocess
import unittest

import tests  # noqa: F401  (puts the bot on sys.path)
import attest
import common
import pin
import render
import rfqueue
from decide import decide

PIN = "c0dec0dec0dec0dec0dec0dec0dec0dec0dec0de"   # fictional
OK = {"attested": True, "record_ok": True, "reason": ""}


def E(i, pr, author, status="queued", queued="2026-01-01T00:00:00Z", started=None, **kw):
    """An entry; a `record` or `retired` one took the final record unless `record_in` says otherwise."""
    e = {"id": f"pr{pr}-{i:012x}", "pr": pr, "sha": f"{i:040x}", "root": "r", "author": author, "status": status,
         "queued": queued, "started": started, "finished": None, "attempts": 0, "reasons": [], "tree": kw.pop("tree", None)}
    if status in ("record", "retired"):
        e["record_in"] = ["final"]
    e.update(kw)
    return e


F6 = 168800                  # the size factor of a 168,800-byte proof: its size in bytes


def V6(S=1.0, every=True, S_every=None, **kw):
    """A v6 result: `S` in `final` and `S_every` (default `S`: the final proof is the largest) in
    `every`, or (`every=False`) `final` only, with the core's reason."""
    tr = {"final": "S", "every": "S_every"} if every else {"final": "S"}
    sc = {"S": S, "P_total_s": S / F6, "size_factor": F6, "final_pi_bytes": 168800, "tracks": tr}
    if every:
        sc.update(S_every=S if S_every is None else S_every, size_factor_every=F6, max_pi_bytes=168800)
    else:
        sc["tracks_reason"] = {"every": "output 2 rejected by acc"}     # the core's form
    return R(S=S, score=sc, **kw)


def R(verdict="ACCEPT", S=1.0, comparable=True, harness=PIN, **kw):
    r = {"verdict": verdict, "comparable": comparable, "harness_commit": harness, "truncated": False,
         "score": {"S": S, "P_total_s": S, "size_factor": 1.0, "final_pi_bytes": 1,
                   "tracks": {"final": "S", "every": "S"}},
         "reasons": ["r1"]}
    r.update(kw)
    return r


class Queue(unittest.TestCase):
    def st(self, *es):
        s = rfqueue.empty("o/r", PIN)
        s["submissions"] = list(es)
        return s

    def test_fair_order(self):
        s = self.st(E(1, 1, "spam", queued="2026-01-01T00:00:01Z"), E(2, 2, "spam", queued="2026-01-01T00:00:02Z"),
                    E(3, 3, "spam", queued="2026-01-01T00:00:03Z"), E(4, 4, "bob", queued="2026-01-01T00:00:09Z"),
                    E(5, 5, "carol", queued="2026-01-01T00:00:05Z"),
                    E(6, 9, "carol", status="rejected", started="2026-01-01T00:00:00Z"),
                    E(7, 8, "spam", status="rejected", started="2025-12-01T00:00:00Z"))
        # bob never evaluated first; then spam (last start 2025-12) before carol (2026-01); then round robin
        self.assertEqual([e["pr"] for e in rfqueue.order(s)], [4, 1, 5, 2, 3])

    def test_ports_first(self):
        s = self.st(E(1, 1, "a", queued="2026-01-01T00:00:01Z"),
                    E(3, 3, "c", queued="2026-01-01T00:00:09Z", port_of="pr3-000000000009"))
        self.assertEqual([e["pr"] for e in rfqueue.order(s)], [3, 1])
        self.assertTrue(rfqueue.any_queued(self.st(E(5, 5, "e"))))
        self.assertFalse(rfqueue.any_queued(self.st(E(5, 5, "e", status="running"))))
        self.assertNotIn("confirming", common.STATUSES)

    def test_no_cap_per_author(self):
        """There is no cap on an author's evaluations: with nobody else waiting, an author's next entry
        runs whatever that author ran recently; another author's waiting entry goes first (the fair
        order decides who goes next, and caps nothing)."""
        self.assertFalse(any(hasattr(common, k) for k in ("AUTHOR_QUOTA", "QUOTA_WINDOW_S")))
        self.assertFalse(any(hasattr(rfqueue, k) for k in ("over_quota", "started_recently")))
        done = [dict(E(k, k, "ann", status="rejected", started=f"2026-01-02T1{k}:00:00Z"), counted_at=f"2026-01-02T1{k}:00:00Z")
                for k in range(6)]
        fresh = E(7, 7, "ann")
        self.assertEqual([e["pr"] for e in rfqueue.order(self.st(*done, fresh))], [7])
        self.assertEqual([e["pr"] for e in rfqueue.order(self.st(*done, fresh, E(8, 8, "bob")))], [8, 7])

    def test_named_organiser_errors_never_count_against_the_author(self):
        """A run that ended in a named organiser error (fingerprint, lengths, malformed, drift, setup,
        cache, attestation) never counts as the author's start in the fair order, nor uses up the
        entry's one uncounted unnamed ERROR."""
        for kind in common.UNCOUNTED_ERRORS:
            e = E(2, 2, "ann", started="2026-01-02T11:10:00Z")
            self.assertFalse(rfqueue.settle_run(e, kind, error=True), kind)
            self.assertIsNone(rfqueue.counted_start(dict(e, status="queued", verdict="ERROR")), kind)
            self.assertEqual(e.get("generic_errors", 0), 0, kind)
        self.assertTrue(rfqueue.settle_run(E(3, 3, "ann", started="t"), "harness", error=True) is False)  # the first unnamed one
        self.assertIn("malformed", common.UNCOUNTED_ERRORS)       # the runner's record of the stream (v6), not `harness`

    def test_pause_count_needs_two_authors_or_an_entry_proof_error(self):
        """The streak's errors that count toward a pause: every entry-proof one (fingerprint,
        lengths, malformed, setup, cache, attestation), and of the others (drift, harness, unnamed, reaped) one
        per author, so one author's entries never pause the queue alone."""
        x = lambda a, k: {"id": "i", "author": a, "kind": k}  # noqa: E731
        self.assertEqual(rfqueue.pause_count([x("ann", k) for k in ("drift", "harness", "unnamed", "reaped") * 5]), 1)
        self.assertEqual(rfqueue.pause_count([x("ann", "harness"), x("bob", "drift")]), 2)
        for k in common.ENTRY_PROOF_ERRORS:
            self.assertEqual(rfqueue.pause_count([x("ann", k), x("ann", k)]), 2, k)
            self.assertEqual(rfqueue.pause_count([x("ann", "harness"), x("ann", k)]), 2, k)
        self.assertEqual(set(common.ENTRY_PROOF_ERRORS) | {"drift", "harness"}, set(common.ORGANISER_ERRORS))
        s = self.st(E(1, 1, "ann"))
        e = s["submissions"][0]
        for k in range(common.STREAK_CAP + 5):
            self.assertFalse(rfqueue.note_error(s, e, "harness", "t", "why", "u"))
        self.assertEqual((len(s["error_streak"]), s.get("paused")), (common.STREAK_CAP, None))
        self.assertTrue(rfqueue.note_error(s, e, "setup", "t2", "the setup", "u2"))
        self.assertEqual(s["paused"], {"since": "t2", "reason": "the setup", "run_url": "u2"})
        self.assertFalse(rfqueue.note_error(s, e, "setup", "t3", "again", "u3"))   # paused once
        self.assertTrue(rfqueue.clear_errors(s))
        self.assertEqual((s["error_streak"], s.get("paused")), ([], None))
        self.assertFalse(rfqueue.clear_errors(s))
        old = rfqueue.load(json.dumps(dict(s, fingerprint_errors=1)).encode(), "r", s["core"])
        self.assertNotIn("fingerprint_errors", old)

    def test_old_errors_age_out_of_the_pause_count(self):
        """An organiser error noted more than STREAK_WINDOW_S (7 days) before the streak's newest
        no longer counts toward a pause: two unrelated errors weeks apart do not pause the queue;
        two within the window do; an entry with no readable time counts."""
        self.assertEqual(common.STREAK_WINDOW_S, 7 * 86400)
        s = self.st(E(1, 1, "ann"), E(2, 2, "bob"))
        a, b = s["submissions"]
        self.assertFalse(rfqueue.note_error(s, a, "attestation", "2026-11-01T00:00:00Z", "first", "u1"))
        self.assertFalse(rfqueue.note_error(s, b, "reaped", "2026-11-08T00:00:01Z", "eight days on", "u2"))
        self.assertEqual((rfqueue.pause_count(s["error_streak"]), s.get("paused")), (1, None))
        self.assertEqual(s["error_streak"][0]["at"], "2026-11-01T00:00:00Z")
        self.assertTrue(rfqueue.note_error(s, a, "harness", "2026-11-09T00:00:00Z", "within a week", "u3"))
        self.assertEqual(rfqueue.pause_count(s["error_streak"]), 2)                 # bob's and ann's latest
        x = lambda a, k, at=None: dict({"id": "i", "author": a, "kind": k}, **({"at": at} if at else {}))  # noqa: E731
        self.assertEqual(rfqueue.pause_count([x("ann", "setup", "2026-11-01T00:00:00Z"),
                                              x("ann", "setup", "2026-11-07T23:59:59Z")]), 2)
        self.assertEqual(rfqueue.pause_count([x("ann", "setup"), x("bob", "cache", "2026-12-01T00:00:00Z")]), 2)
        body = render.pause_notice(dict(s, paused={"since": "t"}), "https://x/run")
        self.assertIn("2 organiser errors counted since the last run that completed its benchmark", body)
        self.assertNotIn("in a row", body)
        self.assertIn("`2026-11-08T00:00:01Z`", body)

    def test_unnamed_errors_count_after_the_first(self):
        """A catch-all harness ERROR or a reaped run is not counted the first time; the retry's ERROR
        counts (from the first counted start, never refreshed)."""
        e = E(1, 1, "cat", started="2026-01-02T10:00:00Z", attempts=1)
        self.assertFalse(rfqueue.settle_run(e, None, error=True))          # the first unnamed ERROR
        self.assertIsNone(rfqueue.counted_start(dict(e, status="queued", verdict="ERROR")))
        rfqueue.mark_running(e, "2026-01-02T11:00:00Z", "u2")
        self.assertTrue(rfqueue.settle_run(e, None, error=True))           # the retry's: it counts
        self.assertEqual(rfqueue.counted_start(dict(e, status="error")), "2026-01-02T11:00:00Z")
        # a reaped run is an unnamed ERROR too
        r = E(2, 2, "cat", status="running", attempts=1, started="2026-01-02T12:00:00Z")
        s = self.st(r)
        rfqueue.reap(s, "t")
        self.assertEqual((r["status"], r["generic_errors"], r["counted_at"]), ("queued", 1, None))
        r.update(status="running", attempts=2, started="2026-01-02T13:00:00Z")
        rfqueue.reap(s, "t")
        self.assertEqual((r["status"], r["counted_at"]), ("error", "2026-01-02T13:00:00Z"))
        # a retry after a counted run keeps the first counted start
        d = E(3, 3, "cat", started="2026-01-01T09:00:00Z")
        self.assertTrue(rfqueue.settle_run(d))
        rfqueue.mark_running(d, "2026-01-02T09:00:00Z", "u")
        rfqueue.settle_run(d)
        self.assertEqual(d["counted_at"], "2026-01-01T09:00:00Z")
        self.assertIn("counted_at", rfqueue.COMPACT_KEYS)

    def test_supersede_and_hold_never_count(self):
        """An entry superseded or withdrawn (hold) never counts, whatever its last run."""
        now = "2026-01-02T12:00:00Z"
        for st_ in ("superseded", "withdrawn"):
            e = dict(E(1, 1, "dan", status=st_, verdict="ERROR", attempts=1, started="2026-01-02T11:00:00Z"),
                     counted_at="2026-01-02T11:00:00Z")
            self.assertIsNone(rfqueue.counted_start(e), st_)
        s = self.st(E(1, 1, "dan", status="withdrawn", verdict="ERROR", attempts=1, started="2026-01-02T11:00:00Z"))
        e, _ = rfqueue.enqueue(s, E(1, 1, "dan"), now)             # the hold is lifted
        self.assertEqual((e["status"], e["attempts"]), ("queued", 0))
        self.assertIsNone(rfqueue.counted_start(e))

    def test_retried_entry_takes_the_fair_order(self):
        """A re-queued entry keeps its queue time but has no front-of-queue: once its author's
        run counted, another author goes first."""
        s = self.st(dict(E(1, 1, "ann", status="queued", verdict="ERROR", attempts=2, started="2026-01-02T11:00:00Z",
                           queued="2026-01-01T00:00:01Z"), counted_at="2026-01-02T11:00:00Z", generic_errors=2),
                    E(2, 2, "bob", queued="2026-01-01T00:00:05Z"))
        self.assertEqual([e["pr"] for e in rfqueue.order(s)], [2, 1])
        s["submissions"][0]["counted_at"] = None                    # a run that did not count: its place is kept
        self.assertEqual([e["pr"] for e in rfqueue.order(s)], [1, 2])

    def test_never_evaluated_first_in_queue_order(self):
        s = self.st(E(1, 1, "b", queued="2026-01-01T00:00:02Z"), E(2, 2, "a", queued="2026-01-01T00:00:03Z"))
        self.assertEqual([e["pr"] for e in rfqueue.order(s)], [1, 2])

    def test_supersede_withdraw_requeue(self):
        s = self.st()
        a, ch = rfqueue.enqueue(s, E(1, 7, "x"), "t1")
        self.assertTrue(ch)
        b, ch = rfqueue.enqueue(s, E(2, 7, "x"), "t2")
        self.assertEqual(rfqueue.find(s, a["id"])["status"], "superseded")
        self.assertEqual(b["queued"], "t2")
        self.assertEqual(rfqueue.withdraw(s, 7, "t3", "closed"), [b["id"]])
        c, ch = rfqueue.enqueue(s, E(2, 7, "x"), "t4")
        self.assertTrue(ch)
        self.assertEqual((c["status"], c["queued"]), ("queued", "t4"))
        _, ch = rfqueue.enqueue(s, E(2, 7, "x"), "t5")      # idempotent
        self.assertFalse(ch)
        rfqueue.find(s, c["id"])["status"] = "rejected"
        _, ch = rfqueue.enqueue(s, E(2, 7, "x"), "t6")      # an evaluated commit is never re-queued
        self.assertFalse(ch)
        e, ch = rfqueue.add_invalid(s, E(3, 7, "x"), ["bad"], "t7")
        self.assertEqual(e["status"], "invalid")
        self.assertFalse(rfqueue.add_invalid(s, E(3, 7, "x"), ["bad"], "t8")[1])

    def test_reap_and_attempts(self):
        s = self.st(E(1, 1, "x", status="running", attempts=1), E(2, 2, "y", status="running", attempts=2))
        self.assertEqual(len(rfqueue.reap(s, "t")[0]), 2)
        self.assertEqual([e["status"] for e in s["submissions"]], ["queued", "error"])

    def test_duplicates(self):
        s = self.st(E(1, 1, "alice", tree="T", status="withdrawn"), E(2, 2, "bob", tree="U", status="accepted"),
                    E(3, 3, "bob", tree="V", status="queued"), E(4, 4, "eve", tree="W", status="invalid"),
                    E(5, 5, "bob", tree="X", status="error"))
        self.assertIn("another author", rfqueue.duplicate_of(s, "new", 9, "mallory", "T"))
        self.assertIsNone(rfqueue.duplicate_of(s, "new", 9, "alice", "T"))
        self.assertIn("already evaluated", rfqueue.duplicate_of(s, "new", 2, "bob", "U"))
        self.assertIn("queued in #3", rfqueue.duplicate_of(s, "new", 9, "bob", "V"))
        self.assertIsNone(rfqueue.duplicate_of(s, "new", 3, "bob", "V"))     # the same PR: superseded instead
        self.assertIsNone(rfqueue.duplicate_of(s, "new", 9, "mallory", "W"))
        self.assertIsNone(rfqueue.duplicate_of(s, "new", 5, "bob", "X"))     # an organiser ERROR may be retried
        self.assertIn("another author", rfqueue.duplicate_of(s, "new", 9, "mallory", "X"))   # by its author only
        s["submissions"] += [E(6, 6, "bob", tree="Y", status="running")]
        self.assertIn("being evaluated", rfqueue.duplicate_of(s, "new", 6, "bob", "Y"))    # an empty push meanwhile

    def test_a_copied_prover_tree_is_a_copy(self):
        """The copy rule also keys on the `prover/` tree: another author's root with the same prover/
        (new NOTES, Lean or root name) came first and is a copy, whatever became of the first; the
        author's own prover under a new root is allowed; an invalid entry never counts."""
        s = self.st(E(1, 1, "alice", tree="T", prover_tree="P", status="superseded"),
                    E(2, 2, "eve", tree="U", prover_tree="Q", status="invalid"))
        self.assertIn("the same prover/ as pr1-", rfqueue.duplicate_of(s, "new", 9, "bob", "T2", "P"))
        self.assertIn("the same root as pr1-", rfqueue.duplicate_of(s, "new", 9, "bob", "T", "P2"))
        self.assertIsNone(rfqueue.duplicate_of(s, "new", 9, "alice", "T2", "P"))      # her own prover, a new root
        self.assertIsNone(rfqueue.duplicate_of(s, "new", 9, "bob", "T2", "Q"))        # an invalid entry: never
        self.assertIsNone(rfqueue.duplicate_of(s, "new", 9, "bob", "T2", None))
        # compaction keeps the prover tree for the rule
        self.assertIn("prover_tree", rfqueue.COMPACT_KEYS)

    def test_the_earliest_queued_owner_of_a_prover_wins(self):
        """The heavy review's snipe.py: bob copies alice's queued prover (one comment changed: a new
        prover/ tree, the same binary), runs first in the fair order and takes the record. Alice's run
        of that binary is not barred by bob's record (she showed it first): the record is set aside
        and she is compared as if it had not been taken. A record of the same binary by the same
        author, or queued first, bars it, as before."""
        alice = E(2, 2, "alice", queued="2026-01-03T00:00:00Z", status="running", prover_tree="PA")
        bob = E(3, 3, "bob", "record", queued="2026-01-03T01:00:00Z", finished="2026-01-04T00:00:00Z",
                harness_commit=PIN, prover_tree="PB", prover_sha256="c" * 64)
        old = E(4, 4, "carol", "record", queued="2025-12-01T00:00:00Z", finished="2025-12-02T00:00:00Z",
                harness_commit=PIN, prover_sha256="d" * 64, record_in=["final", "every"],
                score={"S": 10.0, "S_every": 10.0, "tracks": {"final": "S", "every": "S_every"}})
        s = self.st(old, alice, bob)
        self.assertEqual(rfqueue.standing(s, PIN)["final"], bob)
        keys = {("prover_sha256", "c" * 64), ("prover_tree", "PA")}
        self.assertEqual(rfqueue.prover_owner(s, alice, keys), ({}, [bob["id"]]))
        self.assertEqual(rfqueue.standing(s, PIN, [bob["id"]])["final"], old)       # compared with carol's record
        d = decide(R(S=9.0, prover_sha256="c" * 64), OK, PIN, rfqueue.standing(s, PIN, [bob["id"]]), 1, {})
        self.assertEqual((d["status"], d["record_of"]["final"]), ("record", old["id"]))
        # the sources hash matches too
        bob["prover_sha256"], bob["prover_sources_sha256"] = "e" * 64, "f" * 64
        self.assertEqual(rfqueue.prover_owner(s, alice, {("prover_sources_sha256", "f" * 64)}), ({}, [bob["id"]]))
        # queued after bob's record, or bob's own: barred
        late = E(5, 5, "alice", queued="2026-01-05T00:00:00Z", status="running")
        self.assertEqual(rfqueue.prover_owner(self.st(old, bob, late), late, {("prover_sha256", "e" * 64)}),
                         ({"e" * 64: bob["id"]}, []))
        again = E(6, 6, "bob", queued="2025-01-01T00:00:00Z", status="running")
        self.assertEqual(rfqueue.prover_owner(self.st(old, bob, again), again, {("prover_sha256", "e" * 64)})[0],
                         {"e" * 64: bob["id"]})
        # alice's earlier entry with the same prover/ tree (a later push of hers) keeps her first time
        late["prover_tree"] = "PA"
        s = self.st(old, dict(alice, status="superseded"), bob, late)
        self.assertEqual(rfqueue.prover_owner(s, late, {("prover_sha256", "e" * 64), ("prover_tree", "PA")}),
                         ({}, [bob["id"]]))
        # decide bars by the sources hash as well as the binary's
        d = decide(R(S=1.0, prover_sha256="1" * 64, entry={"prover_sources_sha256": "f" * 64}), OK, PIN, {}, 1,
                   {"f" * 64: bob["id"]})
        self.assertEqual(d["status"], "accepted")
        self.assertTrue(any("never a new record" in r for r in d["reasons"]))

    def test_records_per_pin_and_retirement(self):
        s = self.st(E(1, 1, "a", status="record", finished="2026-01-01", harness_commit=PIN),
                    E(2, 2, "b", status="record", finished="2026-01-02", harness_commit="c" * 40))
        self.assertEqual(rfqueue.current_record(s, PIN, "final")["pr"], 1)
        self.assertEqual(rfqueue.current_record(s, "c" * 40, "final")["pr"], 2)
        self.assertIsNone(rfqueue.current_record(s, "d" * 40, "final"))
        self.assertIsNone(rfqueue.current_record(s, PIN, "every"))       # it took the final record only
        self.assertFalse(rfqueue.retire(s["submissions"][0], "every", "t", "x"))
        self.assertTrue(rfqueue.retire(s["submissions"][0], "final", "t", "x"))
        self.assertFalse(rfqueue.retire(s["submissions"][0], "final", "t", "x"))   # once
        self.assertIsNone(rfqueue.current_record(s, PIN, "final"))   # a retired record never stands again
        self.assertEqual(s["submissions"][0]["status"], "retired")
        self.assertEqual([e["pr"] for e in rfqueue.records(s)], [2, 1])
        # two records at one pin: retiring the newest, the one it beat stands again; never a retired one
        a = E(3, 3, "a", status="record", finished="2026-01-03", harness_commit=PIN)
        b = E(4, 4, "b", status="record", finished="2026-01-04", harness_commit=PIN)
        s = self.st(a, b)
        self.assertIs(rfqueue.current_record(s, PIN, "final"), b)
        rfqueue.retire(b, "final", "t", "x")
        self.assertIs(rfqueue.current_record(s, PIN, "final"), a)
        rfqueue.retire(a, "final", "t", "x")
        self.assertIsNone(rfqueue.current_record(s, PIN, "final"))
        self.assertEqual(rfqueue.due_ports(s, "c" * 40), {})

    def test_dump_names_the_standing_record(self):
        st = rfqueue.empty("o/r", PIN)
        none = {"final": None, "every": None}
        self.assertEqual(json.loads(rfqueue.dump(st))["record"], none)
        st["submissions"] += [E(1, 1, "a", "record", harness_commit=PIN, finished="2026-01-01T00:00:01Z"),
                              E(2, 2, "b", "record", harness_commit="1" * 40, finished="2026-01-01T00:00:02Z")]
        self.assertEqual(json.loads(rfqueue.dump(st))["record"], dict(none, final="pr1-000000000001"))   # the other pin's never stands
        st["submissions"][0]["status"] = "retired"
        self.assertEqual(json.loads(rfqueue.dump(st))["record"], none)

    def test_port(self):
        s = self.st(E(1, 1, "a", status="record", finished="2026-01-01", harness_commit=PIN, tag="rf-source/x"))
        p = rfqueue.port(s, 1, "c" * 40, "now")
        self.assertEqual((p["id"], p["status"], p["port_of"], p["tag"]), (s["submissions"][0]["id"] + "-cccccccc", "queued",
                                                                         s["submissions"][0]["id"], "rf-source/x"))
        self.assertTrue(common.ID_RE.match(p["id"]))
        self.assertIsNone(rfqueue.port(s, 1, "c" * 40, "now"))     # once
        self.assertIsNone(rfqueue.port(s, 1, PIN, "now"))          # the same pin: nothing to port

    def test_due_port(self):
        rec = E(1, 1, "a", status="record", finished="2026-01-01", harness_commit=PIN, tag="rf-source/x")
        s = self.st(rec, E(2, 2, "b", status="accepted", finished="2026-01-02", harness_commit=PIN))
        self.assertIsNone(rfqueue.due_port(s, PIN))                 # it stands at its own pin
        self.assertIs(rfqueue.due_port(s, "c" * 40), rec)
        p = rfqueue.port(s, 1, "c" * 40, "now", o=rec)
        self.assertIsNone(rfqueue.due_port(s, "c" * 40))            # once, whatever its verdict
        p["status"] = "rejected"
        self.assertIsNone(rfqueue.due_port(s, "c" * 40))
        self.assertIs(rfqueue.due_port(s, "d" * 40), rec)           # the next pin: the last standing record
        rfqueue.retire(rec, "final", "t", "x")
        self.assertIsNone(rfqueue.due_port(s, "d" * 40))            # a retired record is not ported
        # a new season: an earlier season's record (a track not in TRACKS) stays in the history, unported
        old = E(3, 3, "c", status="record", finished="2026-01-03", harness_commit=PIN, tag="rf-source/y",
                record_in=["sum", "product"])
        s = self.st(old)
        self.assertEqual((rfqueue.standing(s, PIN)["sum"], rfqueue.due_ports(s, "d" * 40)), (old, {}))
        self.assertEqual(rfqueue.standing(s, "d" * 40), {"final": None, "every": None, "product": None, "sum": None})

    def test_tracks_records_retirement_and_ports(self):
        """Records per track: an entry may hold one track's record or both; retirement is per track;
        a pin move ports each track's record (one port for an entry that holds both), and a port is a
        candidate only in the tracks whose record it carries."""
        a = E(1, 1, "a", "record", finished="2026-01-01", harness_commit=PIN, tag="rf-source/a", record_in=["final", "every"])
        b = E(2, 2, "b", "record", finished="2026-01-02", harness_commit=PIN, tag="rf-source/b", record_in=["every"])
        s = self.st(a)
        self.assertEqual(rfqueue.standing(s, PIN), {"final": a, "every": a})
        self.assertEqual(rfqueue.due_ports(s, "c" * 40), {"final": a, "every": a})
        p = rfqueue.port(s, 1, "c" * 40, "now", o=a)
        self.assertEqual(p["port_tracks"], ["final", "every"])                 # one port for both
        self.assertEqual(rfqueue.due_ports(s, "c" * 40), {})
        s = self.st(a, b)
        self.assertEqual(rfqueue.standing(s, PIN), {"final": a, "every": b})
        self.assertEqual(rfqueue.due_ports(s, "c" * 40), {"final": a, "every": b})
        self.assertIs(rfqueue.due_port(s, "c" * 40), a)
        self.assertEqual(rfqueue.port(s, 1, "c" * 40, "now", o=a)["port_tracks"], ["final"])
        self.assertIs(rfqueue.due_port(s, "c" * 40), b)
        self.assertEqual(rfqueue.port(s, 2, "c" * 40, "now", o=b)["port_tracks"], ["every"])
        self.assertIsNone(rfqueue.due_port(s, "c" * 40))
        # retirement of one track: the entry keeps the other's crown; the retired track falls back to
        # the newest record of the track that is not retired (the one the retired record beat)
        s = self.st(a, b)
        self.assertTrue(rfqueue.retire(b, "every", "t", "x"))
        self.assertEqual((b["status"], rfqueue.standing(s, PIN)), ("retired", {"final": a, "every": a}))
        self.assertEqual(rfqueue.due_ports(s, "c" * 40), {"final": a, "every": a})   # a retired record is not ported
        self.assertTrue(rfqueue.retire(a, "every", "t", "x"))
        self.assertEqual((a["status"], a["retired_in"].keys() == {"every"}), ("record", True))
        self.assertEqual(rfqueue.standing(s, PIN), {"final": a, "every": None})     # every record of it retired
        self.assertEqual(rfqueue.due_ports(s, "c" * 40), {"final": a})
        self.assertEqual([e["id"] for e in rfqueue.records(s, "every")], [b["id"], a["id"]])
        self.assertEqual([e["id"] for e in rfqueue.records(s, "final")], [a["id"]])
        self.assertTrue(rfqueue.retire(a, "final", "t", "x"))
        self.assertEqual(a["status"], "retired")
        # the decision: per track, against that track's standing record, each with its own score
        both = {"S": 10.0, "S_every": 10.0, "tracks": {"final": "S", "every": "S_every"}}
        ra = dict(a, status="record", retired_in={}, record_in=["final", "every"], score=both)
        rf = dict(b, status="record", retired_in={}, record_in=["final"], score={"S": 8.0, "tracks": {"final": "S"}})
        d = decide(V6(S=9.0), OK, PIN, {"final": ra, "every": ra}, 1)
        self.assertEqual((d["status"], d["took"], d["record_of"]), ("record", ["final", "every"], {"final": ra["id"], "every": ra["id"]}))
        d = decide(V6(S=9.0, S_every=9.9), OK, PIN, {"final": ra, "every": ra}, 1)   # a large intermediate proof
        self.assertEqual((d["status"], d["took"], d["against"]["every"]["S"]), ("record", ["final"], 9.9))
        self.assertEqual(common.track_scores(d["score"]), {"final": 9.0, "every": 9.9})
        d = decide(V6(S=9.0, every=False), OK, PIN, {"final": ra, "every": ra}, 1)   # eligible for final only
        self.assertEqual((d["status"], d["took"], d["against"]["every"]), ("record", ["final"], None))
        self.assertIn("not scored in every: output 2 rejected by acc", d["reasons"])
        one = V6(S=9.0, every=False)
        one["score"]["tracks_reason"] = "a reason for every track left out"    # one string: also read
        self.assertIn("not scored in every: a reason for every track left out", decide(one, OK, PIN, {}, 1)["reasons"])
        d = decide(V6(S=9.0), OK, PIN, {"final": rf, "every": ra}, 1)         # a final-only record is faster
        self.assertEqual((d["status"], d["took"], d["record_of"]), ("record", ["every"], {"final": None, "every": ra["id"]}))
        self.assertEqual((d["against"]["final"]["beats"], d["against"]["every"]["beats"]), (False, True))
        self.assertFalse(any("not scored" in r for r in d["reasons"]))
        d = decide(V6(S=9.0), OK, PIN, {"final": ra, "every": None}, 1)
        self.assertEqual((d["status"], d["took"], d["against"]["every"]), ("record", ["final", "every"], None))
        d = decide(V6(S=11.0), OK, PIN, {"final": ra, "every": ra}, 1)
        self.assertEqual((d["status"], d["took"]), ("accepted", []))
        d = decide(V6(S=9.0), OK, PIN, {}, 1, tracks=["every"])     # a port of the every record
        self.assertEqual((d["status"], d["took"]), ("record", ["every"]))
        self.assertTrue(any("candidate only in" in r for r in d["reasons"]))
        d = decide(V6(S=1.0, prover_sha256="p" * 64), OK, PIN, {}, 1, {"p" * 64: b["id"]})
        self.assertEqual((d["status"], d["took"]), ("accepted", []))             # the binary of either track's record
        d = decide(R(S=9.0, score={"S": 9.0}), OK, PIN, {"final": ra, "every": ra}, 1)   # an earlier season's result: the sum alone
        self.assertEqual((d["status"], d["took"], d["against"]["final"]), ("record", ["sum"], None))
        d = decide(R(score={"S": 9.0, "X": 0.0, "tracks": {"final": "S", "every": "X"}}), OK, PIN, {}, 1)   # no positive every score
        self.assertEqual(d["took"], ["final"])
        d = decide(V6(S=0.0), OK, PIN, {}, 1)
        self.assertEqual(d["status"], "unranked")

    def test_score_sanitiser_keeps_the_tracks(self):
        """`tracks` and the fields it names survive the sanitiser whatever the number and order of the
        other keys: 60 filler keys in front, and a v6 score (core_score.json: S, P_total_s,
        size_factor, final_pi_bytes, S_every, size_factor_every, max_pi_bytes, pass_totals_s,
        median_pass, tracks and diagnostics at M = 16, n = 2^18, the size factors the proof sizes
        in bytes, made-up numbers;
        replace it with the core's mock smoke once the core computes this score)."""
        from decide import clean_score
        import os
        raw = {f"filler_{k:02d}": float(k) for k in range(60)}
        raw.update(S=3.0, x=1, S_old=2.0, tracks={"every": "S", "final": "S", "old": "S_old", "Bad": "x", "z": "tracks"})
        sc = clean_score(raw)
        self.assertEqual((sc["tracks"], sc["S"], sc["S_old"]), ({"every": "S", "final": "S", "old": "S_old"}, 3.0, 2.0))
        self.assertEqual(common.track_scores(sc), {"final": 3.0, "every": 3.0, "old": 2.0})
        self.assertEqual(decide(R(score=raw), OK, PIN, {}, 1)["took"], ["final", "every", "old"])
        with open(os.path.join(os.path.dirname(__file__), "core_score.json")) as f:
            core = json.load(f)
        self.assertEqual(clean_score(core), core)
        self.assertEqual(common.track_scores(clean_score(core)), {"final": core["S"], "every": core["S_every"]})
        self.assertIsNone(clean_score(None))

    def test_score_fields(self):
        sc = {"S": 2.0, "S_product": 3.0, "tracks": {"every": "S", "product": "S_product", "final": "S"}}
        self.assertEqual(common.score_fields(sc), [("final", "S", 2.0), ("every", "S", 2.0), ("product", "S_product", 3.0)])
        self.assertEqual(common.score_fields({"S": 2.0, "S_product": 3.0}), [("sum", "S", 2.0)])   # no tracks: an earlier season's sum
        self.assertEqual(common.score_fields({"S": 2.0, "x": 1.0, "tracks": {"Bad Name": "x", "new": "x", "z": "tracks",
                                                                              "w": "missing"}}), [("new", "x", 1.0)])
        self.assertEqual(common.score_fields(None), [])

    def test_migrate_version_1(self):
        """A version-1 state (one record, the sum's) is read as version 2 and rewritten at once."""
        v1 = {"version": 1, "core": PIN, "margin": common.MARGIN, "record": "pr2-000000000002", "submissions": [
            E(1, 1, "a", "retired", harness_commit=PIN, finished="2026-01-01", retired="2026-01-03", record_of=None,
              against=None),
            E(2, 2, "b", "record", harness_commit=PIN, finished="2026-01-02", record_of="pr1-000000000001",
              against={"record": "pr1-000000000001", "S": 1.0, "S_record": 2.0, "gain": 0.5, "beats": True}),
            E(3, 3, "c", "rejected", record_of=None, against=None)]}
        for e in v1["submissions"]:
            e.pop("record_in", None)
        st = rfqueue.load(json.dumps(v1).encode(), "o/r", PIN)
        self.assertTrue(st["_stale"])
        a, b, c = st["submissions"]
        self.assertEqual((a["record_in"], a["retired_in"], b["record_in"], "record_in" in c), (["sum"], {"sum": "2026-01-03"}, ["sum"], False))
        self.assertEqual((b["record_of"], b["against"]["sum"]["S_record"], c["record_of"], c["against"]),
                         ({"sum": "pr1-000000000001"}, 2.0, {"sum": None}, {"sum": None}))
        out = json.loads(rfqueue.dump(st))
        self.assertEqual((out["version"], out["record"]), (2, {"final": None, "every": None, "sum": "pr2-000000000002"}))

    def test_compaction_and_large_state(self):
        """A flood of pushes keeps the state bounded; a large state loads and orders fast."""
        es = []
        for k in range(3000):
            es.append(E(k + 1, 7, "spam", status="superseded", queued=f"2026-01-01T00:{k // 60:02d}:{k % 60:02d}Z",
                        notes=f"notes/{k}.md", reasons=["r" * 300] * 20, title="t" * 200))
        es.append(E(99999, 7, "spam", status="queued", queued="2026-01-02T00:00:00Z"))
        s = self.st(*es)
        dropped = rfqueue.compact(s)
        self.assertEqual(len(dropped), 3000)
        self.assertEqual(len(rfqueue.of_pr(s, 7)), common.MAX_HEADS_PER_PR + 1)
        self.assertTrue(all(set(e) <= set(rfqueue.COMPACT_KEYS) for e in s["submissions"] if e["status"] == "superseded"))
        big = self.st(*[E(k + 1, k + 1, f"u{k % 500}", status="rejected" if k % 3 else "queued",
                          started="2026-01-01T00:00:00Z" if k % 3 else None, reasons=["x" * 300] * 5)
                        for k in range(20000)])
        raw = rfqueue.dump(big)
        self.assertGreater(len(raw), 30 << 20)
        import time
        t = time.monotonic()
        st = rfqueue.load(raw, "o/r", PIN)
        self.assertEqual(len(rfqueue.order(st)), 6667)
        self.assertLess(time.monotonic() - t, 20)

    def test_load_rejects_foreign_state(self):
        with self.assertRaises(ValueError):
            rfqueue.load(b'{"version": 3, "submissions": []}', "o/r", PIN)
        with self.assertRaises(ValueError):
            rfqueue.load(b'{"version": 1, "submissions": [{"id": "x", "status": "hacked"}]}', "o/r", PIN)
        with self.assertRaises(ValueError):       # not a status of this format
            rfqueue.load(b'{"version": 1, "submissions": [{"id": "x", "status": "confirming"}]}', "o/r", PIN)
        old = rfqueue.load(json.dumps({"version": 1, "core": PIN, "margin": common.MARGIN, "record_wins": 2,
                                       "submissions": []}).encode(), "o/r", PIN)
        self.assertTrue(old["_stale"])            # a state that holds record_wins is rewritten
        self.assertNotIn("record_wins", json.loads(rfqueue.dump(old)))


class Decide(unittest.TestCase):
    rec = {"id": "pr1-aaaaaaaaaaaa", "sha": "a" * 40, "root": "r", "score": {"S": 10.0, "tracks": {"final": "S", "every": "S"}}}
    recs = {"final": rec, "every": rec}

    def test_first_record_and_verdicts(self):
        self.assertEqual(decide(R(), OK, PIN, None, 1)["status"], "record")
        self.assertEqual(decide(R("REJECT"), OK, PIN, None, 1)["status"], "rejected")
        self.assertEqual(decide(R("PROVISIONAL"), OK, PIN, None, 1)["status"], "provisional")
        unranked = dict(OK, record_ok=False)      # verify-record.sh is never asked about a non-comparable ACCEPT
        self.assertEqual(decide(R(comparable=False), unranked, PIN, None, 1)["status"], "unranked")
        self.assertEqual(decide(R(comparable=False, truncated=True), unranked, PIN, None, 1)["status"], "unranked")
        self.assertEqual(decide(R(S=0.0), OK, PIN, None, 1)["status"], "unranked")
        self.assertEqual(decide(R(verdict="WIN"), OK, PIN, None, 2)["verdict"], "ERROR")

    def test_error_requeue_once(self):
        d = decide(R("ERROR"), OK, PIN, None, 1)
        self.assertEqual((d["status"], d["requeue"]), ("queued", True))
        d = decide(R("ERROR"), OK, PIN, None, 2)
        self.assertEqual((d["status"], d["requeue"]), ("error", False))
        self.assertEqual(decide(None, {"attested": False}, PIN, None, 2)["status"], "error")

    def test_provenance(self):
        bad = {"attested": False, "record_ok": False, "reason": "nope"}
        self.assertEqual(decide(R(), bad, PIN, None, 1)["status"], "queued")
        self.assertEqual(decide(R(), dict(OK, record_ok=False), PIN, None, 2)["status"], "error")
        self.assertEqual(decide(R(harness="b" * 40), OK, PIN, None, 2)["status"], "error")
        for v in ("REJECT", "PROVISIONAL"):       # an unattested result is never published as such
            d = decide(R(v), bad, PIN, None, 1)
            self.assertEqual((d["status"], d["verified"]), ("queued", False))
            self.assertTrue(any("not verified" in r for r in d["reasons"]))

    def test_record_rule(self):
        """The record rule: S < (1 - MARGIN) * S_record, against the standing record's own score."""
        self.assertEqual(common.MARGIN, 0.02)                       # the owner's margin, pinned
        m, edge = common.MARGIN, (1 - common.MARGIN) * 10.0         # the boundary, as the rule computes it
        d = decide(R(S=edge - 0.01), OK, PIN, self.recs, 1)          # just inside: a record
        self.assertEqual((d["status"], d["record_of"]["final"], d["requeue"], d["took"]), ("record", self.rec["id"], False, ["final", "every"]))
        self.assertEqual(d["record_of"], {"final": self.rec["id"], "every": self.rec["id"]})    # one S, both tracks
        self.assertAlmostEqual(d["against"]["final"]["gain"], m + 0.001)
        a = d["against"]["final"]
        self.assertEqual((a["record"], a["S_record"], a["beats"]), (self.rec["id"], 10.0, True))
        d = decide(R(S=edge), OK, PIN, self.recs, 1)                 # exactly (1 - MARGIN) * S_record: strict, not a record
        self.assertEqual((d["status"], d["record_of"]["final"], d["took"]), ("accepted", None, []))
        self.assertFalse(d["against"]["final"]["beats"])
        self.assertTrue(any("needs more than 2%" in r for r in d["reasons"]))
        d = decide(R(S=edge + 0.01), OK, PIN, self.recs, 1)          # just outside: within the margin
        self.assertEqual((d["status"], d["against"]["final"]["beats"]), ("accepted", False))
        self.assertEqual(decide(R(S=9.9), OK, PIN, self.recs, 1)["status"], "accepted")   # 1 % faster is not enough
        self.assertEqual(decide(R(S=9.7), OK, PIN, self.recs, 1)["status"], "record")     # 3 % faster is
        self.assertEqual(decide(R(S=11.0), OK, PIN, self.recs, 1)["status"], "accepted")
        self.assertEqual(decide(R(S=1.0), OK, PIN, self.recs, 1, margin=0.5)["status"], "record")
        d = decide(R(S=1.0, prover_sha256="p" * 64), OK, PIN, self.recs, 1, {"p" * 64: "pr0-000000000000"})
        self.assertEqual(d["status"], "accepted")
        for res in (R(S=1.0, comparable=False), R(S=1.0, truncated=True, comparable=False)):
            self.assertEqual(decide(res, dict(OK, record_ok=False), PIN, self.recs, 1)["status"], "unranked")
        self.assertEqual(decide(R("REJECT"), OK, PIN, self.recs, 1)["status"], "rejected")
        self.assertEqual(decide(R("ERROR"), OK, PIN, self.recs, 1)["status"], "queued")
        d = decide(R("ERROR", organiser_error="malformed"), OK, PIN, self.recs, common.MAX_ATTEMPTS)
        self.assertEqual((d["status"], d["requeue"], d["organiser_error"]), ("queued", True, "malformed"))
        self.assertTrue(any("a malformed stream record" in r and "does not count as an attempt" in r for r in d["reasons"]))
        for k in ("duel", "duel_now", "wins", "record_failed", "retire_record", "confirm_retry", "duel_retry", "cpu"):
            self.assertNotIn(k, d)

    def test_confirmation(self):
        """A record candidate is confirmed by a second run of the same commit: crowned in the tracks
        both runs take, with the worse score; else accepted; an organiser-side end leaves it pending."""
        from decide import candidate, confirmed
        first = candidate(decide(R(S=9.0), OK, PIN, self.recs, 1), PIN, "https://run/1", "results/x.json")
        self.assertEqual((first["took"], first["pin"]), (["final", "every"], PIN))
        c = confirmed(first, decide(R(S=9.5), OK, PIN, self.recs, 1))
        self.assertEqual((c["status"], c["took"], common.track_scores(c["score"])), ("record", ["final", "every"],
                                                                                   {"final": 9.5, "every": 9.5}))
        self.assertEqual((c["record_of"]["final"], c["against"]["final"]["S"]), (self.rec["id"], 9.5))
        c = confirmed(first, decide(R(S=8.0), OK, PIN, self.recs, 1))     # a better confirmation: the first run's 9.0
        self.assertEqual((c["status"], common.track_scores(c["score"])["final"], c["against"]["final"]["S"]), ("record", 9.0, 9.0))
        c = confirmed(first, decide(V6(S=9.0, every=False), OK, PIN, self.recs, 1))      # confirmed in final only
        self.assertEqual((c["status"], c["took"]), ("record", ["final"]))
        self.assertIn("not confirmed in every", c["reasons"][0])
        # not confirmed: accepted if the confirmation is an ACCEPT that does not beat the record; else
        # the entry's status is the confirmation's (a REJECT is rejected, an unranked ACCEPT unranked)
        for d2, why, status in ((decide(R(S=9.9), OK, PIN, self.recs, 1), "does not beat", "accepted"),
                                (decide(R("REJECT"), OK, PIN, self.recs, 1), "verdict is REJECT", "rejected"),
                                (decide(R("PROVISIONAL"), OK, PIN, self.recs, 1), "PROVISIONAL", "provisional"),
                                (decide(R(comparable=False), dict(OK, record_ok=False), PIN, self.recs, 1), "unranked",
                                 "unranked")):
            c = confirmed(first, d2)
            self.assertEqual((c["status"], c["took"], c["record_of"]), (status, [], {"final": None, "every": None}))
            self.assertIn(why, c["reasons"][0])
        c = confirmed(first, decide(R(S=9.9), OK, PIN, self.recs, 1))
        self.assertEqual((common.track_scores(c["score"])["final"], c["score_run"], c["against"]["final"]["S"]),
                         (9.9, "confirmation", 9.9))                     # the worse run's score and comparison
        rej = decide(R("REJECT", score=None), OK, PIN, self.recs, 1)
        c = confirmed(first, rej)
        self.assertEqual((c["score"], c["score_run"]), (None, "confirmation"))     # the REJECT's (no score)
        c = confirmed(first, decide(R(S=9.95), OK, PIN, self.recs, 1))
        self.assertEqual(c["score_run"], "confirmation")
        c = confirmed(candidate(decide(R(S=9.97), OK, PIN, {}, 1), PIN, "u"), decide(R(S=9.9), OK, PIN, self.recs, 1))
        self.assertEqual(c["status"], "accepted")
        self.assertIsNone(confirmed(first, decide(R("ERROR"), OK, PIN, self.recs, 1)))             # retried, still pending
        self.assertIsNone(confirmed(first, decide(R(), {"attested": False}, PIN, self.recs, 1)))
        # S and S_every order the two runs differently: each track keeps its own worse run
        first = candidate(decide(V6(S=9.0, S_every=9.4), OK, PIN, self.recs, 1), PIN, "https://run/1")
        c = confirmed(first, decide(V6(S=9.1, S_every=9.3), OK, PIN, self.recs, 1))
        self.assertEqual((c["status"], c["took"], common.track_scores(c["score"])),
                         ("record", ["final", "every"], {"final": 9.1, "every": 9.4}))
        self.assertEqual((c["against"]["final"]["S"], c["against"]["every"]["S"]), (9.1, 9.4))
        self.assertEqual(c["score"]["tracks"], {"final": "S", "every": "S_every"})
        # every part shown with a track's score is of the run that gave it: the score object is the
        # lead track's (final) worse run, whole; every's fields are the first run's, in by_track
        self.assertEqual((c["score_run"], c["score"]["P_total_s"], c["score"]["S"]), ("confirmation", 9.1 / F6, 9.1))
        self.assertEqual(set(c["score"]["by_track"]), {"every"})
        bt = c["score"]["by_track"]["every"]
        self.assertEqual((bt["S_every"], bt["P_total_s"], c["score"]["S_every"]), (9.4, 9.0 / F6, 9.4))
        self.assertNotIn("tracks", bt)
        c2 = confirmed(first, decide(V6(S=9.2, S_every=9.5), OK, PIN, self.recs, 1))     # one run worse in both
        self.assertEqual((c2["score_run"], "by_track" in c2["score"], c2["score"]["S_every"]), ("confirmation", False, 9.5))
        self.assertIn("final: 9.0000 s*B, then 9.1000 s*B; every: 9.4000 s*B, then 9.3000 s*B", c["reasons"][0])
        none = candidate(decide(R(S=50.0), OK, PIN, {}, 1), PIN, "u")                     # no record stood: any ACCEPT confirms
        self.assertEqual(confirmed(none, decide(R(S=60.0), OK, PIN, {}, 1))["status"], "record")

    def test_cache_retry(self):
        """A REJECT that restored record modules is retried without the cache only when the cache can
        have caused it: at the certificate or at a badge check (`reject_stage`); a result without
        `reject_stage` (an earlier core) is retried as before."""
        from decide import cache_check, cache_check_stands, cache_retry, reject_stage
        used = {"certificate": {"record_cache": {"restored": ["M"]}}}
        legacy = lambda **kw: dict(R("REJECT", score=None), **used, **kw)  # noqa: E731  (an earlier core: no stage, no v6 marker)
        self.assertTrue(cache_retry(legacy(), {}, True))
        self.assertFalse(cache_retry(legacy(), {}, False))                       # an unverified result: never
        self.assertFalse(cache_retry(legacy(), {"record_cache": False}, True))
        self.assertFalse(cache_retry(dict(R("ACCEPT"), **used), {}, True))
        self.assertFalse(cache_retry(R("REJECT", score=None), {}, True))
        for stage in ("certificate", "check"):
            self.assertTrue(cache_retry(legacy(reject_stage=stage), {}, True), stage)
            self.assertFalse(cache_retry(dict(R("REJECT", score=None), reject_stage=stage), {}, True), stage)   # nothing restored
        for stage in ("prover", "request", "timed-pass", "stream-cap", None, "other"):
            self.assertFalse(cache_retry(legacy(reject_stage=stage), {}, True), stage)
        # this rules' core without a stage (a REJECT path it forgot): final, unless the certificate was rejected
        for marker in ({"stream": {"leaf_data": {"xof": "shake256"}}}, {"score": {"S": 1.0, "pass_totals_s": [1.0]}},
                       {"score": {"S": 1.0, "S_every": 1.1, "tracks": {"final": "S", "every": "S_every"}}}):
            self.assertIsNone(reject_stage(dict(R("REJECT"), **marker)))
            self.assertFalse(cache_retry(legacy(**marker), {}, True), marker)
            rej = dict(legacy(**marker), certificate={"status": "reject", "record_cache": {"restored": ["M"]}})
            self.assertEqual(reject_stage(rej), "certificate")
            self.assertTrue(cache_retry(rej, {}, True))
        self.assertEqual(reject_stage(legacy()), "legacy")
        # a `check` REJECT keeps its badge for the retry; an identical badge after the clean rebuild: it stands
        b = {"verify": "a" * 64}
        first = dict(legacy(reject_stage="check"), certificate={"record_cache": {"restored": ["M"]}, "badge_sha256": b})
        pend = cache_check(first, "u1", ["r"])
        self.assertEqual(pend, {"run_url": "u1", "badge_sha256": b, "reasons": ["r"]})
        self.assertIsNone(cache_check(legacy(reject_stage="certificate"), "u1", []))
        self.assertTrue(cache_check_stands(pend, {"certificate": {"badge_sha256": dict(b)}}))
        self.assertFalse(cache_check_stands(pend, {"certificate": {"badge_sha256": {"verify": "b" * 64}}}))
        self.assertFalse(cache_check_stands(pend, {"certificate": {}}))
        self.assertFalse(cache_check_stands({"badge_sha256": None}, {"certificate": {"badge_sha256": b}}))

    def test_untrusted_fields_cleaned(self):
        d = decide(R(reasons=["x" * 1000, "\u202eevil\nline"] * 30,
                     score={"S": 1.0, "deep": {"a": {"b": {"c": {"d": 1}}}}, "s": "\x00" * 500}), OK, PIN, None, 1)
        self.assertLessEqual(len(d["reasons"]), 20)
        self.assertTrue(all(len(r) <= 300 and r.isprintable() for r in d["reasons"]))
        self.assertLessEqual(len(d["score"]["s"]), 200)


class Render(unittest.TestCase):
    def test_sanitisers(self):
        self.assertEqual(common.code_span("a`b @me [x](y) <img>"), "`a'b @me [x](y) <img>`")
        self.assertTrue(all(32 <= ord(c) < 127 for c in common.code_span("é\u202e\x07")))
        self.assertEqual(common.clean("a\u202eb\tc", 10), "a?b c")
        self.assertEqual(len(common.clean("x" * 500, 200)), 200)

    def test_status_description(self):
        e = {"status": "rejected", "verdict": "REJECT", "score": None}
        self.assertEqual(render.status_for(e), ("failure", "REJECT: rejected"))
        e = {"status": "accepted", "verdict": "ACCEPT", "score": {"S": 2.0, "tracks": {"final": "S"}}}
        self.assertEqual(render.status_for(e), ("success", "ACCEPT: accepted (did not beat the record), S = 2.0000 s (final)"))
        e = {"status": "record", "verdict": "ACCEPT", "record_in": ["every"],
             "score": {"S": 1.23456, "tracks": {"final": "S", "every": "S"}}}
        self.assertEqual(render.status_for(e), ("success", "ACCEPT: new record (every), S = 1.2346 s (final, every)"))
        e = {"status": "record", "verdict": "ACCEPT", "record_in": ["final", "every"],      # this season's rule
             "score": {"S": 4358812.471, "S_every": 5173251.074, "P_total_s": 15.592, "size_factor": 279552,
                       "final_pi_bytes": 279552, "tracks": {"final": "S", "every": "S_every"}}}
        self.assertEqual(render.status_for(e), ("success", "ACCEPT: new record (final, every), S = 4358812.4710 s*B "
                                                "(final), S_every = 5173251.0740 s*B (every)"))
        e["score"]["size_ref"] = 524288                                     # an earlier v6 season's exponential factor
        self.assertIn("S = 4358812.4710 s (final)", render.status_for(e)[1])
        e = {"status": "accepted", "verdict": "ACCEPT", "score": {"S": 2.0}}     # an earlier season's result
        self.assertEqual(render.status_for(e)[1], "ACCEPT: accepted (did not beat the record), S = 2.0000 s (sum)")
        self.assertLessEqual(len(render.status_for({"status": "x" * 500})[1]), 140)

    def test_comment_has_no_live_markdown_from_reasons(self):
        e = {"id": "pr1-aaaaaaaaaaaa", "status": "rejected", "verdict": "REJECT", "reasons": ["`](http://evil) @owner"],
             "verified": True}
        body = render.publish_comment(e, "https://run")
        self.assertIn("- `'](http://evil) @owner`", body)
        self.assertNotIn("``", body)
        e = {"id": "pr2-aaaaaaaaaaaa", "status": "accepted", "verdict": "ACCEPT", "verified": True,
             "score": {"S": 1345410.0, "P_total_s": 7.92, "size_factor": 169875, "final_pi_bytes": 169875, "M": 16,
                       "pass_totals_s": [7.95, 7.92, 7.9], "median_pass": 2, "tracks": {"final": "S"}},
             "against": {"final": {"record": "pr1-aaaaaaaaaaaa", "S": 1345410.0, "S_record": 1359000.0, "gain": 0.01, "beats": False},
                         "every": None}}
        body = render.publish_comment(e, "https://run")
        self.assertIn("Against the final record `pr1-aaaaaaaaaaaa`: 1345410.0000 s·B against 1359000.0000 s·B, gain +1.0%", body)
        self.assertIn("S = 1345410.0000 s·B = P_total 7.9200 s × final proof 169875 bytes (final: P_total · |π_M|), "
                      "M = 16\n", body)
        self.assertIn("\nP_total: pass 2's total, the median of the timed passes' totals 7.9500 s, 7.9200 s, 7.9000 s\n", body)
        self.assertNotIn("S_every", body)                                   # final only
        self.assertIn("Tracks: final (not every: the reasons below say why)", body)
        e["score"].update(S_every=1779624.0, size_factor_every=224700, max_pi_bytes=224700, tracks={"final": "S", "every": "S_every"})
        body = render.publish_comment(e, "https://run")
        self.assertIn("\nS_every = 1779624.0000 s·B = P_total × largest proof 224700 bytes (every: P_total · max |π_i|)\n", body)
        self.assertIn("Tracks: final, every\n", body)
        self.assertNotIn("duel", body.lower())
        # an earlier v6 season's result (`size_ref`): its exponential factor, in seconds
        e["score"] = {"S": 9.9, "P_total_s": 7.92, "size_factor": 1.25, "final_pi_bytes": 168800, "M": 16, "S_every": 10.89,
                      "size_factor_every": 1.375, "max_pi_bytes": 240900, "pass_totals_s": [7.95, 7.92, 7.9], "median_pass": 2,
                      "size_ref": 524288, "tracks": {"final": "S", "every": "S_every"}}
        e["against"] = {"final": {"record": "pr1-aaaaaaaaaaaa", "S": 9.9, "S_record": 10.0, "gain": 0.01, "beats": False}}
        body = render.publish_comment(e, "https://run")
        self.assertIn("Against the final record `pr1-aaaaaaaaaaaa`: 9.9000 s against 10.0000 s, gain +1.0%", body)
        self.assertIn("S = 9.9000 s = P_total 7.9200 s × size factor 1.2500 (final: 2^(|π_M|/512 KiB), final proof "
                      "168800 bytes), M = 16\n", body)
        self.assertIn("\nS_every = 10.8900 s = P_total × size factor 1.3750 (every: 2^(max |π_i|/512 KiB), largest "
                      "proof 240900 bytes)\n", body)

    def test_notes_md_fence(self):
        st = rfqueue.empty("o/r", PIN)
        st["submissions"] = [E(1, 1, "a", status="accepted", notes="notes/1.md", finished="2026-01-02"),
                             E(2, 2, "b", status="record", notes="notes/2.md", finished="2026-01-03", score={"S": 2.0}),
                             E(3, 3, "c", status="superseded", notes="notes/3.md")]
        body = {"notes/1.md": "~~~~~~\n## pr9-000000000000 · fake · @owner · record\n".encode(), "notes/2.md": b"two",
                "notes/3.md": b"three"}
        md = render.notes_md(st, body.get, "o/r").decode()
        self.assertLess(md.index("pr2-"), md.index("pr1-"))
        self.assertNotIn("three", md)
        self.assertIn("~~~~~~~markdown", md)       # a fence longer than any in the notes
        lines = md.splitlines()
        self.assertEqual(sum(1 for x in lines if x.startswith("## ")), 3)    # the bot's two and the forged one
        # the forged header is inside the fence
        i = lines.index("## pr9-000000000000 · fake · @owner · record")
        self.assertEqual(lines[i - 2], "~~~~~~~markdown")

    def test_records_json(self):
        st = rfqueue.empty("o/r", PIN)
        st["submissions"] = [E(1, 1, "a", status="record", finished="2026-01-01", harness_commit=PIN),
                             E(2, 2, "b", status="record", finished="2026-01-02", harness_commit=PIN),
                             E(3, 3, "c", status="accepted", harness_commit=PIN)]
        st["submissions"][1]["record_in"] = ["final", "every"]
        r = json.loads(render.records_json(st, PIN))
        self.assertEqual((r["version"], r["record"]["final"]["pr"], r["record"]["every"]["pr"], [h["pr"] for h in r["history"]["final"]],
                          r["history"]["every"], r["margin"], r["core"]), (2, 2, 2, [1], [], common.MARGIN, PIN))
        self.assertNotIn("record_wins", r)
        empty = json.loads(render.records_json(rfqueue.empty("o/r", PIN), PIN))
        self.assertEqual((empty["record"], empty["history"]), ({"final": None, "every": None}, {"final": [], "every": []}))
        r = json.loads(render.records_json(st, "c" * 40))       # another pin: no standing record, the history kept
        self.assertEqual((r["record"], [h["pr"] for h in r["history"]["final"]], [h["pr"] for h in r["history"]["every"]]),
                         ({"final": None, "every": None}, [2, 1], [2]))


class Pin(unittest.TestCase):
    W = ("jobs:\n  evaluate:\n    uses: scaraven/recursion.fast/.github/workflows/evaluate.yml@{a}\n"
         "    with:\n      core_ref: {b}\n  publish:\n    steps:\n      - with:\n          ref: {b}   # THE PIN\n")

    def test_pins(self):
        self.assertEqual(pin.pins_of(self.W.format(a=PIN, b=PIN), PIN), (PIN, []))
        self.assertIsNone(pin.pins_of(self.W.format(a=PIN, b="c" * 40), PIN)[0])
        self.assertIsNone(pin.pins_of(self.W.format(a=PIN, b=PIN), "c" * 40)[0])
        self.assertIsNone(pin.pins_of(self.W.format(a="main", b="main"), "main")[0])
        two = self.W.format(a=PIN, b=PIN) + "  x:\n    uses: scaraven/recursion.fast/.github/workflows/other.yml@main\n"
        self.assertIsNone(pin.pins_of(two, PIN)[0])
        self.assertIsNone(pin.pins_of(self.W.format(a=PIN, b=PIN) + "      core_ref: " + PIN + "\n", PIN)[0])
        # the publish job's core checkout is the fourth place (a literal: wfcheck refuses a step-output ref)
        self.assertIsNone(pin.pins_of(self.W.format(a=PIN, b=PIN).replace("ref: " + PIN + "   # THE PIN",
                                                                           "ref: " + "c" * 40 + "   # THE PIN"), PIN)[0])
        self.assertIsNone(pin.pins_of(self.W.format(a=PIN, b=PIN).replace("   # THE PIN", ""), PIN)[0])

    def test_core_actions_pinned_by_sha(self):
        core = ("jobs:\n  a:\n    steps:\n      - uses: actions/checkout@" + "1" * 40 + "  # v4\n"
                "      - uses: ./local\n        with: {x: 1}\n")
        self.assertEqual(pin.tag_problems(core), [])
        bad = core + "      - uses: actions/cache/save@v4\n      -   uses: 'actions/x@main'\n      - uses: actions/cache/save@v4\n"
        self.assertEqual(len(pin.tag_problems(bad)), 2)
        self.assertIn("actions/cache/save at v4", pin.tag_problems(bad)[0])

    def test_core_inputs(self):
        """The core's evaluate.yml takes every input the bot passes and requires none it does not pass
        (no incumbent_* input)."""
        import os
        top = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
        with open(os.path.join(top, pin.WORKFLOW)) as f:
            ours = f.read()
        inp = lambda n, req="false": f"      {n}: {{ type: string, required: {req} }}\n"  # noqa: E731
        core = "on:\n  workflow_call:\n    inputs:\n" + "".join(inp(n, "true" if n in ("entry_repo", "core_ref") else "false")
                                                       for n in pin.OUR_INPUTS) + "    outputs:\n"
        self.assertEqual(pin.inputs_problems(ours, core), [])
        self.assertFalse(any(k.startswith("incumbent") for k in pin.OUR_INPUTS))
        self.assertIn("requires the input incumbent_sha", " ".join(pin.inputs_problems(ours, core.replace(
            "    outputs:", inp("incumbent_sha", "true") + "    outputs:"))))
        self.assertIn("has no input record_cache", " ".join(pin.inputs_problems(ours, core.replace(inp("record_cache"), ""))))
        extra = ours.replace("      record_cache:", "      incumbent_sha: x\n      record_cache:")
        self.assertIn("passes incumbent_sha", " ".join(pin.inputs_problems(extra, core + inp("incumbent_sha"))))

    def test_repin_records(self):
        old = {"version": 1, "core": PIN, "margin": 0.02, "record": {"id": "pr1-000000000001"},
               "history": [{"id": "pr0-000000000000"}]}
        r = json.loads(pin.repin_records(json.dumps(old).encode(), "c" * 40))     # version 1: the sum's record
        self.assertEqual((r["version"], r["core"], r["record"], [h["id"] for h in r["history"]["sum"]], r["history"]["final"]),
                         (2, "c" * 40, {"final": None, "every": None, "sum": None}, ["pr1-000000000001", "pr0-000000000000"], []))
        two = {"version": 2, "core": PIN, "margin": 0.02, "record": {"sum": {"id": "pr1-000000000001"}, "product": {"id": "pr2-000000000002"}},
               "history": {"sum": [{"id": "pr0-000000000000"}], "product": []}}
        r = json.loads(pin.repin_records(json.dumps(two).encode(), "c" * 40))     # a new season: the old tracks are history
        self.assertEqual((r["record"], [h["id"] for h in r["history"]["sum"]], [h["id"] for h in r["history"]["product"]]),
                         ({"final": None, "every": None, "product": None, "sum": None}, ["pr1-000000000001", "pr0-000000000000"],
                          ["pr2-000000000002"]))
        self.assertEqual((r["history"]["final"], r["history"]["every"]), ([], []))
        six = {"version": 2, "core": PIN, "margin": 0.02, "record": {"final": {"id": "pr3-000000000003"}, "every": None},
               "history": {"final": [], "every": [], "sum": [], "product": [{"id": "pr2-000000000002"}]}}
        r = json.loads(pin.repin_records(json.dumps(six).encode(), "c" * 40))     # an empty old track is dropped
        self.assertEqual((r["record"], [h["id"] for h in r["history"]["final"]], list(r["history"])),
                         ({"final": None, "every": None, "product": None}, ["pr3-000000000003"], ["final", "every", "product"]))
        launch = render.records_json(rfqueue.empty("o/r", PIN), PIN)
        self.assertEqual(pin.repin_records(launch, "c" * 40), render.records_json(rfqueue.empty("o/r", "c" * 40), "c" * 40))
        # a file of an earlier launch (another margin, the removed record_wins) re-pins to what the bot writes
        v4 = json.dumps({"version": 1, "core": PIN, "margin": 0.03, "record_wins": 2, "record": None, "history": []},
                        indent=1).encode() + b"\n"
        self.assertEqual(pin.repin_records(v4, "c" * 40), render.records_json(rfqueue.empty("o/r", "c" * 40), "c" * 40))

    def test_repository_files(self):
        import os
        top = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
        p, problems = pin.read(top)
        self.assertTrue(p, problems)


RF = "rf-light"          # the server's runners carry exactly one label, rf-bench or rf-light
# 20 shapes GitHub would run on an rf-* runner for a fork-controlled event, and more: each must be refused
VIOLATIONS = {
    "plain": f"on:\n  pull_request:\njobs:\n  a:\n    runs-on: {RF}\n    steps: []\n",
    "runs-on block list": "on:\n  pull_request:\njobs:\n  a:\n    runs-on:\n      - self-hosted\n      - rf-light\n    steps: []\n",
    "matrix runs-on": ("on:\n  pull_request:\njobs:\n  a:\n    strategy:\n      matrix:\n        os: [[self-hosted, rf-light]]\n"
                       "    runs-on: ${{ matrix.os }}\n    steps: []\n"),
    "vars runs-on": "on:\n  pull_request:\njobs:\n  a:\n    runs-on: ${{ vars.RUNNER }}\n    steps: []\n",
    "expr runs-on": ("on:\n  pull_request:\njobs:\n  a:\n    runs-on: ${{ github.event_name == 'push' && 'ubuntu-24.04' || 'rf-light' }}\n"
                     "    steps: []\n"),
    "on flow mapping": f"on: {{pull_request: {{}}, push: {{}}}}\njobs:\n  a:\n    runs-on: {RF}\n    steps: []\n",
    "on quoted keys": f"on:\n  \"pull_request\":\njobs:\n  a:\n    runs-on: {RF}\n    steps: []\n",
    "on space colon": f"on :\n  pull_request:\njobs:\n  a:\n    runs-on: {RF}\n    steps: []\n",
    "4-space indent": f"on:\n    pull_request:\njobs:\n    a:\n        runs-on: {RF}\n        steps: []\n",
    "job flow mapping": f"on:\n  pull_request:\njobs:\n  a: {{ runs-on: {RF}, steps: [] }}\n",
    "local reusable": "on:\n  pull_request:\njobs:\n  a:\n    uses: ./.github/workflows/local.yml\n",
    "other repo reusable": "on:\n  pull_request:\njobs:\n  a:\n    uses: scaraven/recursion.fast-submissions/.github/workflows/evaluate-next.yml@main\n",
    "if double quotes": f"on:\n  pull_request:\njobs:\n  a:\n    if: github.event_name == \"push\"\n    runs-on: {RF}\n    steps: []\n",
    "if braces": f"on:\n  pull_request:\njobs:\n  a:\n    if: ${{{{ github.event_name == 'push' }}}}\n    runs-on: {RF}\n    steps: []\n",
    "if on PR label": f"on:\n  pull_request:\njobs:\n  a:\n    if: contains(github.event.pull_request.labels.*.name, 'ok')\n    runs-on: {RF}\n    steps: []\n",
    "issues event": f"on:\n  issues:\njobs:\n  a:\n    runs-on: {RF}\n    steps: []\n",
    "discussion_comment": f"on:\n  discussion_comment:\njobs:\n  a:\n    runs-on: {RF}\n    steps: []\n",
    "fork/watch event": f"on:\n  watch:\n  fork:\njobs:\n  a:\n    runs-on: {RF}\n    steps: []\n",
    "prt checks out PR head": ("on:\n  pull_request_target:\njobs:\n  a:\n    runs-on: [self-hosted, rf-light]\n    steps:\n"
                               "      - uses: actions/checkout@sha\n        with: { ref: ${{ github.event.pull_request.head.sha }} }\n"
                               "      - run: ./run-me.sh\n"),
    "runner group": "on:\n  pull_request:\njobs:\n  a:\n    runs-on:\n      group: organiser\n    steps: []\n",
    # more
    "issue_comment": f"on: issue_comment\njobs:\n  a:\n    runs-on: {RF}\n",
    "workflow_run": f"on:\n  workflow_run:\n    workflows: [x]\njobs:\n  a:\n    runs-on: {RF}\n",
    "on inline list": f"on: [push, pull_request]\njobs:\n  a:\n    runs-on: {RF}\n",
    "push to any branch": f"on:\n  push:\njobs:\n  a:\n    runs-on: {RF}\n",
    "push to a branch pattern": f"on:\n  push:\n    branches: ['**']\njobs:\n  a:\n    runs-on: {RF}\n",
    "push of tags": f"on:\n  push:\n    branches: [main]\n    tags: ['*']\njobs:\n  a:\n    runs-on: {RF}\n",
    "workflow_call": f"on:\n  workflow_call:\njobs:\n  a:\n    runs-on: {RF}\n",
    "guard on an unsafe event": f"on:\n  pull_request:\n  push:\n    branches: [main]\njobs:\n  a:\n    if: github.event_name == 'pull_request'\n    runs-on: {RF}\n",
    "guard on an absent event": f"on:\n  pull_request:\njobs:\n  a:\n    if: github.event_name == 'push'\n    runs-on: {RF}\n",
    "self-hosted string": "on: pull_request\njobs:\n  a:\n    runs-on: self-hosted\n",
    "rf-bench label": "on: pull_request\njobs:\n  a:\n    runs-on: rf-bench\n",
    "two-label list": "on: pull_request\njobs:\n  a:\n    runs-on: [self-hosted, rf-light]\n",
    "hosted label in a list": "on: pull_request\njobs:\n  a:\n    runs-on: [ubuntu-24.04]\n",
    "quoted rf label": "on: pull_request\njobs:\n  a:\n    runs-on: 'rf-light'\n",
    "unknown hosted label": "on: pull_request\njobs:\n  a:\n    runs-on: ubuntu-24.04-arm\n",
    "prt checkout repository": ("on: pull_request_target\njobs:\n  a:\n    runs-on: [self-hosted, rf-light]\n    steps:\n"
                                "      - uses: actions/checkout@sha\n        with:\n          repository: ${{ github.event.pull_request.head.repo.full_name }}\n"),
    "prt head_ref in run": ("on: pull_request_target\njobs:\n  a:\n    runs-on: ubuntu-24.04\n    steps:\n"
                            "      - run: git fetch origin ${{ github.head_ref }} && make\n"),
    "anchor": f"on:\n  pull_request: &x\njobs:\n  a:\n    runs-on: {RF}\n",
    "alias": "on: pull_request\nx: &r ubuntu-24.04\njobs:\n  a:\n    runs-on: *r\n",
    "duplicate key": "on: pull_request\njobs:\n  a:\n    runs-on: ubuntu-24.04\n    runs-on: [self-hosted, rf-light]\n",
    "multi-line flow": f"on: pull_request\njobs:\n  a:\n    runs-on: [self-hosted,\n      rf-light]\n",
    "no on": f"jobs:\n  a:\n    runs-on: {RF}\n",
    "no jobs": "on: pull_request\n",
    "document marker": f"---\non: pull_request\njobs:\n  a:\n    runs-on: {RF}\n",
    "tab indent": "on: pull_request\njobs:\n\ta:\n\t\truns-on: ubuntu-24.04\n",
}
# bypass shapes of rule 4 (pull_request_target and other main-run events), verbatim: every
# VIOLATION must be refused
PRT = "on:\n  pull_request_target:\n"
CO = "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1"
VIOLATION, FINE = "VIOLATION", "fine"
BYPASS = [
    ("reusable under pull_request_target with PR head in job with", VIOLATION,
     PRT + "jobs:\n  a:\n    uses: ./.github/workflows/run.yml\n    with:\n      ref: ${{ github.event.pull_request.head.sha }}\n    secrets: inherit\n"),
    ("reusable under pull_request_target, core evaluate.yml with PR head", VIOLATION,
     PRT + "jobs:\n  a:\n    uses: scaraven/recursion.fast/.github/workflows/evaluate.yml@0000000000000000000000000000000000000000\n    with:\n      entry_ref: ${{ github.event.pull_request.head.sha }}\n"),
    # --- pull_request_target: the PR head as code (all must be refused) ---
    ("prt: checkout head.sha", VIOLATION, PRT + f"jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - uses: {CO}\n        with:\n          ref: ${{{{ github.event.pull_request.head.sha }}}}\n"),
    ("prt: checkout via job env", VIOLATION, PRT + f"jobs:\n  a:\n    runs-on: rf-light\n    env:\n      R: ${{{{ github.event.pull_request.head.sha }}}}\n    steps:\n      - uses: {CO}\n        with:\n          ref: ${{{{ env.R }}}}\n"),
    ("prt: checkout via step env", VIOLATION, PRT + f"jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - uses: {CO}\n        env:\n          R: ${{{{ github.event.pull_request.head.sha }}}}\n        with:\n          ref: ${{{{ env.R }}}}\n"),
    ("prt: checkout HEAD upper-case", VIOLATION, PRT + f"jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - uses: {CO}\n        with:\n          ref: ${{{{ github.event.pull_request.HEAD.sha }}}}\n"),
    ("prt: checkout Pull_Request mixed case", VIOLATION, PRT + f"jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - uses: {CO}\n        with:\n          ref: ${{{{ github.event.Pull_Request.head.sha }}}}\n"),
    ("prt: checkout index syntax", VIOLATION, PRT + f"jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - uses: {CO}\n        with:\n          ref: ${{{{ github.event['pull_request']['head']['sha'] }}}}\n"),
    ("prt: checkout merge_commit_sha", VIOLATION, PRT + f"jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - uses: {CO}\n        with:\n          ref: ${{{{ github.event.pull_request.merge_commit_sha }}}}\n"),
    ("prt: checkout refs/pull/N/merge", VIOLATION, PRT + f"jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - uses: {CO}\n        with:\n          ref: refs/pull/${{{{ github.event.number }}}}/merge\n"),
    ("prt: checkout pull/N/head (no refs/)", VIOLATION, PRT + f"jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - uses: {CO}\n        with:\n          ref: pull/${{{{ github.event.number }}}}/head\n"),
    ("prt: checkout fork repository + branch", VIOLATION, PRT + f"jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - uses: {CO}\n        with:\n          repository: ${{{{ github.event.pull_request.head.repo.full_name }}}}\n          ref: ${{{{ github.event.pull_request.head.ref }}}}\n"),
    ("prt: checkout fork via env", VIOLATION, PRT + f"jobs:\n  a:\n    runs-on: rf-light\n    env:\n      REPO: ${{{{ github.event.pull_request.head.repo.full_name }}}}\n      REF: ${{{{ github.event.pull_request.head.ref }}}}\n    steps:\n      - uses: {CO}\n        with:\n          repository: ${{{{ env.REPO }}}}\n          ref: ${{{{ env.REF }}}}\n"),
    ("prt: checkout by a different action (checkout fork)", VIOLATION, PRT + "jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - uses: someone/checkout@0000000000000000000000000000000000000000\n        with:\n          ref: ${{ github.event.pull_request.head.sha }}\n"),
    ("prt: run fetches pull/N/head via env and executes it", VIOLATION, PRT + "jobs:\n  a:\n    runs-on: rf-light\n    env:\n      N: ${{ github.event.number }}\n    steps:\n      - run: |\n          git init q && cd q && git fetch https://github.com/$GITHUB_REPOSITORY pull/$N/head && git checkout FETCH_HEAD && ./x.sh\n"),
    ("prt: run with head_ref in env, used as code", VIOLATION, PRT + "jobs:\n  a:\n    runs-on: rf-light\n    env:\n      R: ${{ github.head_ref }}\n    steps:\n      - run: git clone -b \"$R\" https://github.com/x/y && ./y/x.sh\n"),
    ("prt: run names the head via index syntax", VIOLATION, PRT + "jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - run: git fetch origin ${{ github.event['pull_request']['head']['sha'] }}\n"),
    ("prt: run names the head via upper case", VIOLATION, PRT + "jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - run: git fetch origin ${{ github.event.pull_request.HEAD.sha }} && git checkout FETCH_HEAD && ./x.sh\n"),
    ("prt: run with toJSON(pull_request) (expression injection)", VIOLATION, PRT + "jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - run: echo '${{ toJSON(github.event.pull_request) }}'\n"),
    ("prt: run with PR title (expression injection)", VIOLATION, PRT + "jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - run: echo \"${{ github.event.pull_request.title }}\"\n"),
    ("prt: with: head.sha to a script action via upper case", VIOLATION, PRT + "jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - uses: actions/github-script@0000000000000000000000000000000000000000\n        with:\n          script: core.info('${{ github.event.pull_request.HEAD.sha }}')\n"),
    ("prt: guarded job (push) with head.sha is not scanned (correct?)", FINE, "on:\n  push:\n    branches: [main]\n  pull_request_target:\njobs:\n  a:\n    if: github.event_name == 'push'\n    runs-on: rf-light\n    steps:\n      - uses: " + CO + "\n        with:\n          ref: ${{ github.event.pull_request.head.sha }}\n"),
    ("issue_comment + checkout refs/pull (pwn on hosted)", VIOLATION, "on: issue_comment\njobs:\n  a:\n    runs-on: ubuntu-latest\n    steps:\n      - uses: " + CO + "\n        with:\n          ref: refs/pull/${{ github.event.issue.number }}/head\n      - run: ./x.sh\n"),
    ("prt: intake-style (allowed)", FINE, PRT + f"jobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - uses: {CO}\n        with:\n          ref: ${{{{ github.sha }}}}\n      - env:\n          PR: ${{{{ github.event.pull_request.number }}}}\n        run: python3 -I bot.py --pr \"$PR\"\n"),
]
ALLOWED = {
    # fetching refs/pull/N/head as data stays allowed (the intake reads pull requests so); `./x` is the base's
    "prt fetches refs/pull as data": ("on: pull_request_target\njobs:\n  a:\n    runs-on: [self-hosted, rf-light]\n    steps:\n"
                             "      - run: |\n          git fetch origin refs/pull/1/head\n          ./x\n"),
    "prt on rf, base checkout": ("on: pull_request_target\njobs:\n  a:\n    runs-on: [self-hosted, rf-light]\n    steps:\n"
                                 "      - uses: actions/checkout@sha\n        with: { ref: \"${{ github.sha }}\", path: bot }\n"
                                 "      - env:\n          PR: ${{ github.event.pull_request.number }}\n"
                                 "          HEAD: ${{ github.event.pull_request.head.sha }}\n        run: ./bot \"$PR\" \"$HEAD\"\n"),
    "pull_request on GitHub-hosted": "on:\n  pull_request:\njobs:\n  a:\n    runs-on: ubuntu-24.04\n    steps: []\n",
    "guarded push job beside a PR job": (f"on:\n  push:\n    branches: [main]\n  pull_request:\njobs:\n  a:\n"
                                         f"    if: github.event_name == 'push'\n    runs-on: {RF}\n  b:\n    runs-on: ubuntu-latest\n"),
    "dispatch, schedule, push to main": (f"on:\n  workflow_dispatch:\n    inputs:\n      pr: {{ description: \"x: y\", required: false }}\n"
                                         f"  schedule:\n    - cron: \"7 * * * *\"\n  push:\n    branches: [main]\n    paths: ['a/**']\n"
                                         f"jobs:\n  a:\n    runs-on: {RF}\n    steps:\n      - name: x\n        run: echo '#1' # c\n"
                                         f"  e:\n    uses: scaraven/recursion.fast/.github/workflows/evaluate.yml@abc\n"),
}


class Workflows(unittest.TestCase):
    """No workflow runs on the organiser's machine for a fork-controlled event
    (`wfcheck.py`, fail-closed); pin-check runs it on a pull request's files before the merge."""

    def test_main_workflows_pass(self):
        import os
        import wfcheck
        top = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
        self.assertEqual(wfcheck.check_dir(top), [])
        d = os.path.join(top, ".github", "workflows")
        self.assertGreaterEqual(len([f for f in os.listdir(d) if wfcheck.is_workflow(f)]), 5)

    def test_every_violation_is_refused(self):
        import wfcheck
        for name, text in VIOLATIONS.items():
            self.assertNotEqual(wfcheck.check_text(name, text), [], name)
        for name, text in ALLOWED.items():
            self.assertEqual(wfcheck.check_text(name, text), [], name)

    def test_rule4_shapes(self):
        """Rule 4 is an allowlist; env: indirection, a reusable job's with:, case, index syntax,
        expression injection and fetched-code execution are refused; the intake's shape passes."""
        import wfcheck
        bad = [(n, t) for n, k, t in BYPASS if k == VIOLATION]
        self.assertGreaterEqual(len(bad), 15)
        for name, text in bad:
            self.assertNotEqual(wfcheck.check_text(name, text), [], name)
        self.assertEqual(wfcheck.check_text("intake-style", dict((n, t) for n, k, t in BYPASS)["prt: intake-style (allowed)"]), [])
        # the expression allowlist in each place it applies
        ok = PRT + "jobs:\n  a:\n    runs-on: rf-light\n    env:\n      N: ${{ github.event.pull_request.number }}\n    steps:\n" \
                   "      - run: echo \"$N\" ${{ github.sha }} ${{ inputs.z }}\n"
        self.assertEqual(wfcheck.check_text("ok", ok), [])
        for frag in ("${{ github.event.pull_request.number }}", "${{ github.event['sha'] }}", "${{ Github.sha }}",
                     "${{ format('{0}', github.sha) }}", "${{ secrets.OTHER }}", "${{ github.event.issue.title }}", "${{ unterminated"):
            self.assertNotEqual(wfcheck.check_text("x", ok.replace("${{ inputs.z }}", frag)), [], frag)
        self.assertNotEqual(wfcheck.check_text("env case", ok.replace("github.event.pull_request.number", "github.event.Pull_Request.number")), [])
        fetch = PRT + "jobs:\n  a:\n    runs-on: rf-light\n    env:\n      N: ${{ github.event.number }}\n    steps:\n" \
                      "      - run: git init -q --bare pr.git && git --git-dir pr.git fetch -q origin refs/pull/$N/head\n"
        self.assertEqual(wfcheck.check_text("fetch as data", fetch), [])            # the intake's way: allowed
        self.assertNotEqual(wfcheck.check_text("then checkout", fetch.rstrip("\n") + " && git checkout FETCH_HEAD\n"), [])
        core = ("on: workflow_dispatch\njobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - uses: " + CO +
                "\n        with:\n          repository: scaraven/recursion.fast\n          ref: " + "a" * 40 + "\n          path: core\n")
        self.assertEqual(wfcheck.check_text("fixed repository at a literal commit", core), [])
        self.assertNotEqual(wfcheck.check_text("at a step's output", core.replace("a" * 40, "${{ steps.pin.outputs.pin }}")), [])
        self.assertNotEqual(wfcheck.check_text("path expression", core.replace("path: core", "path: ${{ env.P }}")), [])
        self.assertNotEqual(wfcheck.check_text("repository expression", core.replace("scaraven/recursion.fast", "${{ inputs.r }}")), [])

    def test_cross_job_shapes(self):
        """env./steps./needs. never in code positions, runs-on/container/services/shell/
        working-directory/defaults scanned, YAML escapes refused, checkout only at a literal commit,
        more code-running commands refused; the known bypass and false rejects stay as accepted."""
        import wfcheck
        from tests import wfcheck_cases as R4
        viol = [(n, t) for n, k, t in R4.cases if k == R4.VIOLATION]
        self.assertGreaterEqual(len(viol), 30)
        for name, text in viol:
            if name not in R4.KNOWN_BYPASS:
                self.assertNotEqual(wfcheck.check_text("w.yml", text), [], name)
        for name, k, text in R4.cases:
            if k == R4.FINE and name not in R4.KNOWN_FALSE_REJECT:
                self.assertEqual(wfcheck.check_text("w.yml", text), [], name)
        for esc in ('run: "echo \\x24{{ github.event.pull_request.title }}"', 'run: "echo \\u0024{{ x }}"', 'run: "a\\nb"'):
            self.assertNotEqual(wfcheck.check_text("esc", "on: workflow_dispatch\njobs:\n  a:\n    runs-on: rf-light\n"
                                                           "    steps:\n      - " + esc + "\n"), [], esc)

    def test_no_workflow_text_stalls_the_check(self):
        """The heavy review's redos.py: KEY_RE was quadratic in a long line without a colon (8 lines of
        64 KiB took 71 s). Every pattern is linear now, a line above 4 KiB is refused before any
        pattern reads it, and the bot runs the check in a subprocess with a time limit."""
        import os
        import tempfile
        import time
        import wfcheck
        line = "a" + " " * 16000 + "b"
        t = time.monotonic()
        self.assertIsNone(wfcheck.KEY_RE.match(line))
        self.assertIsNotNone(wfcheck.KEY_RE.match("key   : value"))
        self.assertEqual(wfcheck._scalar(wfcheck.KEY_RE.match("key   : value").group(1)), "key")
        self.assertEqual(wfcheck._scalar(wfcheck.KEY_RE.match('"k" : v').group(1)), "k")
        big = "on: workflow_dispatch\njobs:\n" + ("a" + " " * 65000 + "b\n") * 8
        self.assertIn("more than 4096 bytes", wfcheck.check_text("x.yml", big)[0])
        head = "on: workflow_dispatch\njobs:\n  a:\n    runs-on: rf-light\n    steps:\n      - run: |\n"
        worst = ["on: workflow_dispatch\njobs:\n" + ("  a" + " " * 4000 + "b\n") * 100,
                 head + ("          " + "git " * 1000 + "\n") * 100,
                 head + ("          " + "${{" * 1300 + "\n") * 100,
                 head + ("          " + "| " * 2000 + "\n") * 100]
        for text in worst:
            wfcheck.check_text("x.yml", text)
        self.assertLess(time.monotonic() - t, 10)
        self.assertEqual(wfcheck.expressions("a ${{ x }} b ${{ y }}${{ z"), [" x ", " y "])
        self.assertTrue(wfcheck.run_makes_code("git fetch x && git \\\ncheckout FETCH_HEAD"))
        self.assertFalse(wfcheck.run_makes_code("git fetch origin refs/pull/1/head\necho checkout"))
        # in a subprocess with a time limit: a timeout is a problem, never a pass
        d = tempfile.mkdtemp(prefix="rf-wf-")
        self.addCleanup(__import__("shutil").rmtree, d, True)
        os.makedirs(os.path.join(d, ".github", "workflows"))
        with open(os.path.join(d, ".github", "workflows", "ok.yml"), "w") as f:
            f.write(ALLOWED["pull_request on GitHub-hosted"])
        g = lambda *a: subprocess.run(["git", "-C", d, *a], capture_output=True, check=True,  # noqa: E731
                                      env={"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t",
                                           "GIT_COMMITTER_EMAIL": "t@t", "PATH": os.environ["PATH"], "HOME": d})
        g("init", "-q")
        g("add", "-A")
        g("commit", "-q", "-m", "x")
        gd = os.path.join(d, ".git")
        self.assertEqual(wfcheck.check_git_limited(gd, "HEAD"), wfcheck.check_git(gd, "HEAD"))
        self.assertEqual(wfcheck.check_git_limited(gd, "HEAD"), [])
        self.assertIn("did not finish within", wfcheck.check_git_limited(gd, "HEAD", timeout=0.001)[0])
        self.assertIn("cannot list", wfcheck.check_git_limited(gd, "0" * 40)[0])

    def test_intake_runs_only_for_events_that_matter(self):
        """intake.yml: an `edited` event runs only when the base changed, a label event only for
        `hold`, and one intake per pull request runs at a time (the newest event's)."""
        import os
        with open(os.path.join(os.path.dirname(__file__), "..", "..", "workflows", "intake.yml")) as f:
            text = f.read()
        import wfcheck
        job = wfcheck.parse(text)["jobs"]["intake"]
        cond = " ".join(job["if"].split())
        for part in ("github.event.action == 'edited' && github.event.changes.base != null",
                     "github.event.label.name == 'hold'", "github.ref == 'refs/heads/main'"):
            self.assertIn(part, cond)
        self.assertEqual(job["concurrency"], {"group": "intake-${{ github.event.pull_request.number || inputs.pr }}",
                                              "cancel-in-progress": "true"})

    def test_size_caps(self):
        """Workflows above 64 KiB per file or 512 KiB in all are refused before any parse."""
        import os
        import tempfile
        import wfcheck
        d = tempfile.mkdtemp(prefix="rf-wf-")
        self.addCleanup(__import__("shutil").rmtree, d, True)
        w = os.path.join(d, ".github", "workflows")
        os.makedirs(w)
        with open(os.path.join(w, "big.yml"), "w") as f:
            f.write("on: workflow_dispatch\njobs:\n  a:\n    runs-on: rf-light\n    steps:\n" + "      - run: echo hi\n" * 4000)
        self.assertTrue(wfcheck.check_dir(d)[0].startswith("the workflows are too large to check"))
        g = lambda *a: subprocess.run(["git", "-C", d, *a], capture_output=True, check=True,  # noqa: E731
                                      env={"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t",
                                           "GIT_COMMITTER_EMAIL": "t@t", "PATH": os.environ["PATH"], "HOME": d})
        g("init", "-q")
        g("add", "-A")
        g("commit", "-q", "-m", "x")
        self.assertTrue(wfcheck.check_git(os.path.join(d, ".git"), "HEAD")[0].startswith("the workflows are too large"))

    def test_yaml_files_and_git_reading(self):
        import os
        import tempfile
        import wfcheck
        d = tempfile.mkdtemp(prefix="rf-wf-")
        self.addCleanup(__import__("shutil").rmtree, d, True)
        w = os.path.join(d, ".github", "workflows")
        os.makedirs(w)
        self.assertEqual(wfcheck.check_dir(d), ["no workflow files found"])
        with open(os.path.join(w, "ok.yml"), "w") as f:
            f.write(ALLOWED["pull_request on GitHub-hosted"])
        self.assertEqual(wfcheck.check_dir(d), [])
        with open(os.path.join(w, "bad.yaml"), "w") as f:          # GitHub runs *.yaml too
            f.write(VIOLATIONS["plain"])
        self.assertEqual(len(wfcheck.check_dir(d)), 1)
        g = lambda *a: subprocess.run(["git", "-C", d, *a], capture_output=True, check=True,  # noqa: E731
                                      env={"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t",
                                           "GIT_COMMITTER_EMAIL": "t@t", "PATH": os.environ["PATH"], "HOME": d})
        g("init", "-q")
        g("add", "-A")
        g("commit", "-q", "-m", "x")
        probs = wfcheck.check_git(os.path.join(d, ".git"), "HEAD")
        self.assertEqual(len(probs), 1)
        self.assertIn("bad.yaml", probs[0])
        # names matched case-insensitively and with surrounding whitespace
        for fn in ("bad.YML", "bad2.Yaml", "bad3.yml "):
            with open(os.path.join(w, fn), "w") as f:
                f.write(VIOLATIONS["plain"])
        self.assertEqual(len(wfcheck.check_dir(d)), 4)
        g("add", "-A")
        g("commit", "-q", "-m", "y")
        self.assertEqual(len(wfcheck.check_git(os.path.join(d, ".git"), "HEAD")), 4)

    def test_pin_check_runs_it_on_pull_requests(self):
        import os
        top = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
        with open(os.path.join(top, ".github", "workflows", "pin-check.yml")) as f:
            text = f.read()
        self.assertIn("base/.github/bot/wfcheck.py --git pr.git FETCH_HEAD", text)


class Attest(unittest.TestCase):
    repo, rid = "o/r", "77"

    def fake(self, rc=0, digest=PIN, uri="https://github.com/o/r/actions/runs/77/attempts/1", vr_rc=0, env="self-hosted"):
        def run(cmd, **kw):
            if cmd[0] == "gh":
                assert "--deny-self-hosted-runners" not in cmd
                out = json.dumps([{"verificationResult": {"signature": {"certificate": {
                    "buildSignerDigest": digest, "buildSignerURI": "u", "runInvocationURI": uri,
                    "runnerEnvironment": env}}}}]).encode()
                return subprocess.CompletedProcess(cmd, rc, out, b"err")
            return subprocess.CompletedProcess(cmd, vr_rc, b"verify-record: OK", b"")
        return run

    def res(self, **kw):
        r = {"verdict": "ACCEPT", "comparable": True, "harness_commit": PIN, "job": "o/r/actions/runs/77/attempts/1"}
        r.update(kw)
        return r

    def test_verify(self):
        v = attest.verify("p", self.res(), self.repo, self.rid, "core", run=self.fake())
        self.assertEqual((v["attested"], v["record_ok"]), (True, True))
        self.assertFalse(attest.verify("p", self.res(), self.repo, self.rid, "core", run=self.fake(rc=1))["attested"])
        self.assertFalse(attest.verify("p", self.res(), self.repo, self.rid, "core", run=self.fake(digest="b" * 40))["attested"])
        self.assertFalse(attest.verify("p", self.res(), self.repo, self.rid, "core",
                                       run=self.fake(uri="https://github.com/o/r/actions/runs/76/attempts/1"))["attested"])
        self.assertFalse(attest.verify("p", self.res(job="o/r/actions/runs/76/attempts/1"), self.repo, self.rid, "core",
                                       run=self.fake())["attested"])
        self.assertFalse(attest.verify("p", self.res(harness_commit=None), self.repo, self.rid, "core", run=self.fake())["attested"])
        # attested on the organiser's self-hosted runner, not a GitHub-hosted one
        v = attest.verify("p", self.res(), self.repo, self.rid, "core", run=self.fake(env="github-hosted"))
        self.assertFalse(v["attested"])
        self.assertIn("self-hosted", v["reason"])
        self.assertFalse(attest.verify("p", self.res(), self.repo, self.rid, "core", run=self.fake(env=None))["attested"])
        v = attest.verify("p", self.res(), self.repo, self.rid, "core", run=self.fake(vr_rc=1))
        self.assertEqual((v["attested"], v["record_ok"]), (True, False))
        v = attest.verify("p", self.res(verdict="REJECT"), self.repo, self.rid, "core", run=self.fake())
        self.assertEqual((v["attested"], v["record_ok"]), (True, False))
        # a non-comparable ACCEPT is attested and never asked of verify-record.sh
        v = attest.verify("p", self.res(comparable=False), self.repo, self.rid, "core", run=self.fake(vr_rc=1))
        self.assertEqual((v["attested"], v["record_ok"]), (True, False))
        # an earlier attempt than the one that selected the entry is refused
        self.assertFalse(attest.verify("p", self.res(), self.repo, self.rid, "core", run=self.fake(), min_attempt=2)["attested"])
        v = attest.verify("p", self.res(job="o/r/actions/runs/77/attempts/2"), self.repo, self.rid, "core",
                          run=self.fake(uri="https://github.com/o/r/actions/runs/77/attempts/2"), min_attempt=2)
        self.assertTrue(v["attested"])


if __name__ == "__main__":
    unittest.main()
