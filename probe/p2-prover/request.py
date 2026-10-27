#!/usr/bin/env python3
"""A runner-like stream `leaf` request (PROVER.md §3): start the prover, wait for `ready`, stage
leaf.json, write `go`, time until `done`, then check proof.bin with the prover's native `acc` and
the flipped-statement canary.   request.py PROVER WORKDIR SOCKET N START_HEX"""
import hashlib, json, os, subprocess, sys, time
prover, work, sock, n, start = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
os.makedirs(work, exist_ok=True)
b2s = lambda m: hashlib.blake2s(m, digest_size=32).digest()
d = bytes.fromhex(start)
for _ in range(n):
    d = b2s(b"C" + d)
stmt = b2s(b"L" + d + n.to_bytes(8, "little")).hex()
vk = subprocess.run([prover, "vk"], capture_output=True, text=True, env=dict(os.environ, RF_ORACLE=sock)).stdout.strip()
open(os.path.join(work, "vk.hex"), "w").write(vk + "\n")
t0 = time.monotonic()
p = subprocess.Popen([prover, "leaf", work], cwd=work, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                     stderr=subprocess.PIPE, text=True, env=dict(os.environ, RF_ORACLE=sock))
assert p.stdout.readline().strip() == "ready", "no ready"
t_ready = time.monotonic() - t0
json.dump({"n": n, "start": start}, open(os.path.join(work, "leaf.json"), "w"))
t1 = time.monotonic()
p.stdin.write("go\n"); p.stdin.flush()
line = p.stdout.readline().strip()
t_req = time.monotonic() - t1
p.wait(timeout=60)
err = p.stderr.read()
ok = subprocess.run([prover, "acc", "--vk", vk, "--stmt", stmt, os.path.join(work, "proof.bin")], capture_output=True, text=True).stdout.strip()
bad = bytearray(bytes.fromhex(stmt)); bad[0] ^= 1
canary = subprocess.run([prover, "acc", "--vk", vk, "--stmt", bad.hex(), os.path.join(work, "proof.bin")], capture_output=True, text=True).stdout.strip()
print(f"LEAF-REQUEST n={n} startup_to_ready_s={t_ready:.3f} request_s={t_req:.3f} done={line=='done'} acc={ok} canary={canary.split(':')[0]} | {err.strip().splitlines()[-1] if err.strip() else ''}", flush=True)
sys.exit(0 if line == "done" and ok == "accept" and canary.startswith("reject") else 1)
