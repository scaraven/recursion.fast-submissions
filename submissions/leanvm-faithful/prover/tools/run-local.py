#!/usr/bin/env python3
"""A local dev runner of the v6 stream (not the harness; no sandbox, no clock rules): starts `rf-oracle`, runs
`prover first` then `prover step` M-1 times through the ready/go/done handshake (service run), then switches the
service to replay mode and runs the stream again with `oracle.key` (a timed-pass imitation), and checks that every
replayed output is byte-identical to the service run's. Also runs `prover kat prf KEY` against the live service.

  python3 -I tools/run-local.py PROVER RF_ORACLE WORKDIR [--n N] [--M M] [--threads T ...] [--pi w|skel]  (RUN_LOCAL_LOG=1 prints each request's log line)

WORKDIR must not exist. Leaf data: SHAKE-256(b"lvm6-local" || step) truncated to 32 n bytes (not the runner's seeds).
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time


def stage_inputs(d, n, step, prev_stmt, prev_bin, vk_hex, key):
    os.makedirs(d)
    with open(os.path.join(d, "vk.hex"), "w") as f:
        f.write(vk_hex + "\n")
    inputs = {"leaf.json": json.dumps({"n": n}).encode(),
              "leaf.bin": hashlib.shake_256(b"lvm6-local" + bytes([step])).digest(32 * n)}
    if prev_stmt is not None:
        inputs["prev.stmt"] = (prev_stmt + "\n").encode()
        inputs["prev.bin"] = prev_bin
    if key is not None:
        inputs["oracle.key"] = (key + "\n").encode()
    return inputs


def request(prover, mode, d, inputs, env):
    p = subprocess.Popen([prover, mode, d], cwd=d, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, env=env)
    t0 = time.monotonic()
    line = p.stdout.readline().decode().strip()
    if line != "ready":
        p.kill()
        raise SystemExit(f"{mode}: no ready ({line!r}): {p.stderr.read().decode()[-2000:]}")
    ready_s = time.monotonic() - t0
    for name, data in inputs.items():          # the runner renames them in at go; here: written just before go
        with open(os.path.join(d, name), "wb") as f:
            f.write(data)
    t1 = time.monotonic()
    p.stdin.write(b"go\n")
    p.stdin.flush()
    line = p.stdout.readline().decode().strip()
    err = p.stderr.read().decode()
    rc = p.wait(timeout=600)
    step_s = time.monotonic() - t1
    if line != "done" or rc != 0:
        raise SystemExit(f"{mode}: rc {rc}, line {line!r}: {err[-3000:]}")
    return open(os.path.join(d, "proof.bin"), "rb").read(), ready_s, step_s, err.strip().splitlines()[-1:]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("prover")
    ap.add_argument("oracle")
    ap.add_argument("work")
    ap.add_argument("--n", type=int, default=6)
    ap.add_argument("--M", type=int, default=4)
    ap.add_argument("--threads", type=int, nargs="*", default=[0])
    ap.add_argument("--pi", default="w")  # w (ws) | skel
    a = ap.parse_args()
    os.makedirs(a.work)
    sock = os.path.join(a.work, "o.sock")
    svc = subprocess.Popen([a.oracle, "--socket", sock], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    vk = None
    while True:
        line = svc.stdout.readline().strip()
        if line.startswith("vk "):
            vk = line[3:]
        if line == "ready":
            break
        if not line and svc.poll() is not None:
            raise SystemExit("rf-oracle died")

    def ctl(cmd, until):
        svc.stdin.write(cmd + "\n")
        svc.stdin.flush()
        out = []
        while True:
            line = svc.stdout.readline().strip()
            out.append(line)
            if line.startswith(until):
                return out

    def stream(tag, key, threads):
        env = {"RF_ORACLE": sock, "PATH": "/nonexistent", "HOME": a.work, "LVM6_PI": a.pi}
        for k in ("LVM_CPU", "LVM6_Q_BLOB"):  # dev pass-through: a forced tier (QEMU hides PCLMULQDQ), a circuit blob
            if k in os.environ:
                env[k] = os.environ[k]
        if threads:
            env["LVM_THREADS"] = str(threads)
        outs, prev_stmt, prev_bin = [], None, None
        for i in range(1, a.M + 1):
            d = os.path.join(a.work, f"{tag}-s{i}")
            inputs = stage_inputs(d, a.n, i, prev_stmt, prev_bin, vk, key)
            mode = "first" if i == 1 else "step"
            f, rs, ss, log = request(a.prover, mode, d, inputs, env)
            ctl("drop", "dropped")
            # the runner's statement, from the prover's own log line (`c <hex>`): this runner trusts it (dev only)
            c = log[0].split(" c ")[1].split()[0]
            print(f"{tag} step {i}: |file| {len(f)} ready {rs:.3f} s step {ss:.3f} s sha256 {hashlib.sha256(f).hexdigest()[:16]}")
            if os.environ.get("RUN_LOCAL_LOG"):
                print("   ", log[0][:600])
            outs.append(f)
            prev_stmt, prev_bin = c, f
        return outs

    base = stream("svc", None, a.threads[0])
    key = ctl("replay", "replay ready")[0].split()[1]
    with open(os.path.join(a.work, "oracle-key.hex"), "w") as f:  # dev: for `refv-full`'s keyed-answer check
        f.write(key + "\n")
    kat = subprocess.run([a.prover, "kat", "prf", key], env={"RF_ORACLE": sock}, capture_output=True, text=True)
    print(kat.stdout.strip() or kat.stderr.strip())
    ok = kat.returncode == 0
    for t in a.threads:
        ctl("replay", "replay ready")
        outs = stream(f"replay-t{t}", key, t)
        same = all(x == y for x, y in zip(base, outs))
        print(f"replay threads {t or 'default'}: {'byte-identical' if same else 'DIFFERENT'} to the service run")
        ok &= same
    print(ctl("stats", "stats")[-1])
    svc.stdin.close()
    svc.wait(timeout=60)
    print("run-local:", "OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
