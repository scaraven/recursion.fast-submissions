#!/usr/bin/env python3
"""End-to-end self-tests of the native prover against the real oracle service (stage F2).

  python3 -I selftest.py --prover BIN --service RF_ORACLE --work DIR [--threads 16]
                         [--r 2] [--n 16] [--m 4] [--sizes 1024,4096] [PART ...]

PART (default `tree stream sizes`): `tree` (the smoke tree: `leaves.json`, `vk.hex`, `prover tree`; every output
accepted by `prover verify-native`, the runner's canaries of every output rejected), `stream` (the
`leaf` / `node` handshake as the runner drives it, `harness/rfh/prover.py` `request`, for M links;
every output and the canaries of the first leaf and node checked), `sizes` (single signed leaves
at the given n), `bench` (`bench-leaf` at each `--bench` n, `--reps` times, with the in-process keyed
oracle and through a fresh service, peak RSS from `/usr/bin/time -v`), `keyed-kat` (a service started
with `--insecure-test-keys K SEED`: `prove-leaf --oracle service` and `--oracle keyed:K` give the
same bytes, so the in-process oracle is the service's `PRF_k`). One service process per part, started with `--socket` in a fresh directory and
stopped by closing its stdin; its `stats` line is printed. Every step has a timeout. The digests
are recomputed here from the starts (`harness/rfh/digest.py`'s layouts), never taken from the
prover. Prints one line per check and `selftest: pass` or exits non-zero.
"""
import argparse
import hashlib
import json
import os
import select
import shutil
import struct
import subprocess
import sys
import time

LOG = []


def say(msg):
    line = f"{time.strftime('%H:%M:%S')} {msg}"
    print(line, flush=True)
    LOG.append(line)


def fail(msg):
    say(f"FAIL {msg}")
    sys.exit(1)


# ---- digests (contract layouts) --------------------------------------------------------------------

def b2s(m):
    return hashlib.blake2s(m, digest_size=32).digest()


def chain_end(s, n):
    d = s
    for _ in range(n):
        d = b2s(b"C" + d)
    return d


def leaf_stmt(h, n):
    return b2s(b"L" + h + n.to_bytes(8, "little"))


def node_stmt(c1, c2):
    return b2s(b"N" + c1 + c2)


# ---- the signed-proof file (FORMAT.md) and the runner's canaries (rfh/checks.py) -------------------

def parse(b):
    off = 0

    def take(n):
        nonlocal off
        if n > len(b) - off:
            raise ValueError
        off += n
        return b[off - n:off]

    def u64():
        return struct.unpack("<Q", take(8))[0]
    try:
        pi = take(u64())
        m = u64()
        if m > len(b):
            return None
        tr = []
        for _ in range(m):
            q = take(u64())
            tr.append((q, take(32)))
        idx = u64()
        ots = [take(32) for _ in range(133)]
        path = [take(32) for _ in range(16)]
    except ValueError:
        return None
    return (pi, tr, idx, ots, path) if off == len(b) else None


def enc(pi, tr, idx, ots, path):
    out = [struct.pack("<Q", len(pi)), pi, struct.pack("<Q", len(tr))]
    for q, a in tr:
        out += [struct.pack("<Q", len(q)), q, a]
    out.append(struct.pack("<Q", idx))
    return b"".join(out + ots + path)


def canaries(data, stmt, sibling=None):
    """The mutations `harness/rfh/checks.py` `canaries` makes of an accepted signed proof."""
    s = parse(data)
    out = [("file+1", stmt, data + b"\x00"), ("file-1", stmt, data[:-1])]
    if s is None:
        return out
    pi, tr, idx, ots, path = s
    flip = bytearray(stmt)
    flip[0] ^= 1
    out.append(("stmt-bit", bytes(flip), data))
    if sibling is not None and sibling != stmt:
        out.append(("swapped-child", sibling, data))
    out.append(("pi+1", stmt, enc(pi + b"\x00", tr, idx, ots, path)))
    if pi:
        out.append(("pi-1", stmt, enc(pi[:-1], tr, idx, ots, path)))
    if tr:
        q, a = tr[0]
        out.append(("trace-answer", stmt, enc(pi, [(q, bytes([a[0] ^ 1]) + a[1:])] + tr[1:], idx, ots, path)))
        q, a = tr[len(tr) // 2]
        mid = tr[:len(tr) // 2] + [(q, a[:31] + bytes([a[31] ^ 0x80]))] + tr[len(tr) // 2 + 1:]
        out.append(("trace-answer-mid", stmt, enc(pi, mid, idx, ots, path)))
    out.append(("trace-extra", stmt, enc(pi, tr + [(b"", bytes(32))], idx, ots, path)))
    out.append(("sig-ots", stmt, enc(pi, tr, idx, [bytes([ots[0][0] ^ 1]) + ots[0][1:]] + ots[1:], path)))
    out.append(("sig-idx", stmt, enc(pi, tr, idx ^ 1, ots, path)))
    return out


# ---- processes -------------------------------------------------------------------------------------

class Service:
    def __init__(self, binary, d, extra=()):
        os.makedirs(d)
        self.dir = d
        self.err = open(os.path.join(d, "service.stderr"), "wb")
        self.p = subprocess.Popen([binary, "--socket", "oracle.sock", *extra], cwd=d, stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, stderr=self.err)
        buf, t = b"", time.monotonic()
        while b"ready\n" not in buf:
            if time.monotonic() - t > 300 or not select.select([self.p.stdout], [], [], 300)[0]:
                self.p.kill()
                fail("service did not become ready")
            c = os.read(self.p.stdout.fileno(), 4096)
            if not c:
                fail("service exited before ready")
            buf += c
        self.info = dict(l.split(" ", 1) for l in buf.decode().splitlines() if " " in l)
        self.vk = bytes.fromhex(self.info["vk"])
        self.sock = os.path.join(d, "oracle.sock")
        say(f"service up: keygen_ms={self.info.get('keygen_ms')} simd={self.info.get('simd')}")

    def stop(self):
        self.p.stdin.close()
        out, _ = self.p.communicate(timeout=120)
        stats = [l for l in out.decode().splitlines() if l.startswith("stats")]
        say(f"service stopped (exit {self.p.returncode}): {stats[0] if stats else '?'}")
        return stats[0] if stats else ""


def env(a, sock):
    e = {"PATH": "/usr/bin:/bin", "RF_ORACLE": sock, "SPARTAN_THREADS": str(a.threads)}
    if a.verbose:
        e["SPARTAN_VERBOSE"] = "1"
    return e


def run(cmd, timeout, **kw):
    t = time.monotonic()
    r = subprocess.run(cmd, capture_output=True, timeout=timeout, **kw)
    return r, time.monotonic() - t


def verify(a, vk, stmt, path):
    r, dt = run([a.prover, "verify-native", vk.hex(), stmt.hex(), path], 600)
    return r.returncode == 0 and r.stdout.startswith(b"accept"), r.stdout.decode().strip(), dt


def info(a, path):
    r, _ = run([a.prover, "info", path], 60)
    return r.stdout.decode().strip()


def check_canaries(a, vk, path, stmt, sib, tag):
    data = open(path, "rb").read()
    d = path + ".canary"
    os.makedirs(d, exist_ok=True)
    bad = []
    for name, c, b in canaries(data, stmt, sib):
        f = os.path.join(d, name)
        open(f, "wb").write(b)
        ok, out, _ = verify(a, vk, c, f)
        if ok:
            bad.append(name)
    if bad:
        fail(f"{tag}: canaries accepted: {bad}")
    say(f"{tag}: {len(canaries(data, stmt, sib))} canaries rejected")


def write_atomic(path, data):
    tmp = path + ".tmp"
    open(tmp, "wb").write(data)
    os.replace(tmp, path)


def request(a, kind, work, sock, vk, inputs, step_s=600):
    """One `leaf` / `node` request driven as the runner does; (seconds, proof bytes, stderr)."""
    os.makedirs(work)
    open(os.path.join(work, "vk.hex"), "w").write(vk.hex() + "\n")
    p = subprocess.Popen([a.prover, kind, work], cwd=work, env=env(a, sock), stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    fd, buf = p.stdout.fileno(), b""

    def wait_line(word, deadline):
        nonlocal buf
        while True:
            lines = buf.split(b"\n")
            if word.encode() in lines[:-1]:
                buf = b"\n".join(lines[lines.index(word.encode()) + 1:])
                return "line"
            left = deadline - time.monotonic()
            if left <= 0:
                return "timeout"
            if select.select([fd], [], [], left)[0]:
                c = os.read(fd, 1 << 16)
                if not c:
                    return "eof"
                buf += c
    if wait_line("ready", time.monotonic() + step_s) != "line":
        p.kill()
        fail(f"{kind}: no ready line; stderr {p.stderr.read()[-500:]!r}")
    t0 = time.monotonic()
    for name, data in inputs.items():
        write_atomic(os.path.join(work, name), data)
    p.stdin.write(b"go\n")
    p.stdin.flush()
    r = wait_line("done", t0 + step_s)
    dt = time.monotonic() - t0
    if r == "eof":
        p.wait(timeout=max(1.0, t0 + step_s - time.monotonic()))
        dt = time.monotonic() - t0
    if r == "timeout":
        p.kill()
        fail(f"{kind}: timeout")
    try:
        p.stdin.close()
    except BrokenPipeError:
        pass
    p.wait(timeout=60)
    err = p.stderr.read().decode(errors="replace")
    if p.returncode != 0:
        fail(f"{kind}: exit {p.returncode}: {err[-500:]}")
    return dt, open(os.path.join(work, "proof.bin"), "rb").read(), err


# ---- parts -----------------------------------------------------------------------------------------

def part_tree(a):
    d = os.path.join(a.work, "tree")
    svc = Service(a.service, os.path.join(d, "svc"))
    try:
        w = os.path.join(d, "work")
        os.makedirs(w)
        starts = [os.urandom(32) for _ in range(1 << a.r)]
        open(os.path.join(w, "leaves.json"), "w").write(json.dumps({"n": a.n, "starts": [s.hex() for s in starts]}))
        open(os.path.join(w, "vk.hex"), "w").write(svc.vk.hex() + "\n")
        r, dt = run([a.prover, "tree", w], 1800, cwd=w, env=env(a, svc.sock))
        say(f"tree r={a.r} n={a.n}: exit {r.returncode} in {dt:.3f} s")
        if a.verbose:
            sys.stdout.write(r.stderr.decode(errors="replace"))
        if r.returncode != 0:
            fail(f"tree: {r.stderr.decode(errors='replace')[-800:]}")
        levels = [[leaf_stmt(chain_end(s, a.n), a.n) for s in starts]]
        while len(levels[-1]) > 1:
            cur = levels[-1]
            levels.append([node_stmt(cur[i], cur[i + 1]) for i in range(0, len(cur), 2)])
        files = [(f"proofs/L{i}.bin", 0, i) for i in range(1 << a.r)]
        files += [(f"proofs/N{l}_{j}.bin", l, j) for l in range(1, a.r) for j in range(1 << (a.r - l))]
        files.append(("root.bin", a.r, 0))
        for rel, l, j in files:
            path = os.path.join(w, rel)
            ok, out, vdt = verify(a, svc.vk, levels[l][j], path)
            say(f"tree {rel}: {out} ({vdt:.3f} s) {info(a, path)}")
            if not ok:
                fail(f"tree {rel} rejected")
        for rel, l, j in files:
            sib = levels[l][j ^ 1] if l < a.r else None
            check_canaries(a, svc.vk, os.path.join(w, rel), levels[l][j], sib, f"tree {rel}")
    finally:
        svc.stop()


def part_stream(a):
    d = os.path.join(a.work, "stream")
    svc = Service(a.service, os.path.join(d, "svc"))
    try:
        starts = [os.urandom(32) for _ in range(a.m + 1)]
        ds = [leaf_stmt(chain_end(s, a.n), a.n) for s in starts]
        prev = None
        for i in range(a.m + 1):
            dt, leaf, err = request(a, "leaf", os.path.join(d, f"leaf{i}"), svc.sock, svc.vk,
                                    {"leaf.json": json.dumps({"n": a.n, "start": starts[i].hex()}).encode()})
            lp = os.path.join(d, f"leaf{i}.bin")
            open(lp, "wb").write(leaf)
            ok, out, _ = verify(a, svc.vk, ds[i], lp)
            say(f"stream leaf {i}: {dt:.4f} s, {out}, {info(a, lp)}")
            if a.verbose:
                sys.stdout.write(err)
            if not ok:
                fail(f"stream leaf {i} rejected")
            if i == 0:
                check_canaries(a, svc.vk, lp, ds[0], None, "stream leaf 0")
                prev = (ds[0], lp)
                continue
            ins = {"child1.stmt": (prev[0].hex() + "\n").encode(), "child1.bin": open(prev[1], "rb").read(),
                   "child2.stmt": (ds[i].hex() + "\n").encode(), "child2.bin": leaf}
            dt, node, err = request(a, "node", os.path.join(d, f"node{i}"), svc.sock, svc.vk, ins)
            c = node_stmt(prev[0], ds[i])
            np_ = os.path.join(d, f"node{i}.bin")
            open(np_, "wb").write(node)
            ok, out, _ = verify(a, svc.vk, c, np_)
            say(f"stream node {i}: {dt:.4f} s, {out}, {info(a, np_)}")
            if a.verbose:
                sys.stdout.write(err)
            if not ok:
                fail(f"stream node {i} rejected")
            if i == 1:
                check_canaries(a, svc.vk, np_, c, None, "stream node 1")
            prev = (c, np_)
    finally:
        svc.stop()


def part_sizes(a):
    d = os.path.join(a.work, "sizes")
    svc = Service(a.service, os.path.join(d, "svc"))
    try:
        for n in a.sizes:
            s = os.urandom(32)
            f = os.path.join(d, f"L-n{n}.bin")
            r, dt = run([a.prover, "prove-signed", s.hex(), str(n), f], 3600, env=env(a, svc.sock))
            if r.returncode != 0:
                fail(f"sizes n={n}: {r.stderr.decode(errors='replace')[-500:]}")
            ok, out, vdt = verify(a, svc.vk, leaf_stmt(chain_end(s, n), n), f)
            say(f"sizes n={n}: {dt:.3f} s, {out} ({vdt:.3f} s), {info(a, f)}")
            if a.verbose:
                sys.stdout.write(r.stderr.decode(errors="replace"))
            if not ok and "proofCap" not in out:
                fail(f"sizes n={n} rejected: {out}")
    finally:
        svc.stop()


def part_keyed_kat(a):
    d = os.path.join(a.work, "keyed-kat")
    key = hashlib.blake2s(b"spartan-srom keyed kat", digest_size=32).digest()
    svc = Service(a.service, os.path.join(d, "svc"), ["--insecure-test-keys", key.hex(), "00" * 32])
    try:
        for n in (1, 16, 64):
            s = hashlib.blake2s(b"start%d" % n, digest_size=32).hexdigest()
            outs = []
            for o in ("service", f"keyed:{key.hex()}"):
                f = os.path.join(d, f"n{n}-{o.split(':')[0]}.bin")
                r, _ = run([a.prover, "prove-leaf", "--oracle", o, s, str(n), f], 600, env=env(a, svc.sock))
                if r.returncode != 0:
                    fail(f"keyed-kat n={n} {o}: {r.stderr.decode(errors='replace')[-300:]}")
                outs.append(open(f, "rb").read())
            if outs[0] != outs[1]:
                fail(f"keyed-kat n={n}: service and in-process keyed proofs differ")
            say(f"keyed-kat n={n}: service and in-process keyed oracle give the same {len(outs[0])} bytes "
                f"(sha256 {hashlib.sha256(outs[0]).hexdigest()[:16]})")
    finally:
        svc.stop()


def timed(a, cmd, envd, timeout):
    """Run under `/usr/bin/time -v`: (stdout, peak RSS in kB, stderr)."""
    r = subprocess.run(["/usr/bin/time", "-v"] + cmd, capture_output=True, timeout=timeout, env=envd)
    err = r.stderr.decode(errors="replace")
    rss = next((int(l.split()[-1]) for l in err.splitlines() if "Maximum resident set size" in l), -1)
    if r.returncode != 0:
        fail(f"{' '.join(cmd)}: exit {r.returncode}: {err[-800:]}")
    return r.stdout.decode(), rss, err


def part_bench(a):
    d = os.path.join(a.work, "bench")
    os.makedirs(d)
    for n in a.bench:
        out, rss, _ = timed(a, [a.prover, "bench-leaf", "--oracle", "keyed", str(n), str(a.reps)], env(a, ""), 7200)
        for l in out.splitlines():
            say(f"bench keyed n={n}: {l}")
        say(f"bench keyed n={n}: peak_rss_kb={rss}")
        svc = Service(a.service, os.path.join(d, f"svc-n{n}"))
        try:
            out, rss, _ = timed(a, [a.prover, "bench-leaf", "--oracle", "service", str(n), str(a.reps)],
                                env(a, svc.sock), 7200)
            for l in out.splitlines():
                say(f"bench service n={n}: {l}")
            say(f"bench service n={n}: peak_rss_kb={rss}")
        finally:
            say(f"bench service n={n}: {svc.stop()}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--prover", required=True)
    ap.add_argument("--service", required=True)
    ap.add_argument("--work", required=True)
    ap.add_argument("--threads", type=int, default=16)
    ap.add_argument("--r", type=int, default=2)
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--m", type=int, default=4)
    ap.add_argument("--sizes", default="1024,4096")
    ap.add_argument("--bench", default="16,1024,4096")
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("parts", nargs="*")
    a = ap.parse_args()
    a.prover, a.service, a.work = map(os.path.abspath, (a.prover, a.service, a.work))
    a.sizes = [int(x) for x in a.sizes.split(",") if x]
    a.bench = [int(x) for x in a.bench.split(",") if x]
    if os.path.exists(a.work):
        shutil.rmtree(a.work)
    os.makedirs(a.work)
    say(f"selftest: prover {a.prover} (sha256 {hashlib.sha256(open(a.prover, 'rb').read()).hexdigest()[:16]})")
    for part in a.parts or ["tree", "stream", "sizes"]:
        {"tree": part_tree, "stream": part_stream, "sizes": part_sizes, "bench": part_bench,
         "keyed-kat": part_keyed_kat}[part](a)
    say("selftest: pass")


if __name__ == "__main__":
    main()
