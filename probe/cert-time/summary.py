"""H-cert probe summary: the build's and each comparator run's wall time and memory peak against the
season's [certificate] caps, the comparator's phases, the top modules by build time and by kernel
time (KReplay).
  python3 -I summary.py OUTDIR"""
import collections, glob, os, re, sys

out = sys.argv[1]
rd = lambda f: open(os.path.join(out, f), errors="replace").read() if os.path.exists(os.path.join(out, f)) else ""
GiB = 2 ** 30
model = next((l.split(":", 1)[1].strip() for l in rd("machine.txt").splitlines() if l.startswith("Model name")), "?")
print(f"cpu: {model}")


def mem(name):
    m = re.search(r"Maximum resident set size \(kbytes\): (\d+)", rd(f"{name}.time"))
    peak = int(rd(f"{name}.peak").strip() or 0)
    ex = re.search(r"Exit status: (\d+)", rd(f"{name}.time"))
    return (peak / GiB if peak else None), (int(m[1]) / 2 ** 20 if m else None), (ex[1] if ex else "?")


def line(name, s, cap, memcap):
    pk, rss, ex = mem(name)
    f = lambda x: f"{x:.2f} GiB" if x else "n/a"
    return (f"{name}: wall {s:.1f} s, cap {cap} s, margin cap/wall {cap / s:.2f}x; cgroup peak {f(pk)} "
            f"(scope cap {memcap}), largest process max RSS {f(rss)}; exit {ex}")


m = re.search(r"([\d.]+)", rd("build.wall"))
if m:
    print(line("build", float(m[1]), int(os.environ.get("BUILD_CAP", "600")), "12G"))

for wall in sorted(glob.glob(os.path.join(out, "comparator*.wall"))):
    name = os.path.basename(wall)[:-5]
    s = float(re.search(r"([\d.]+)", rd(f"{name}.wall"))[1])
    print(line(name, s, 600, "14G"))
    log = rd(f"{name}.log")
    verdict = re.findall(r" (Lean default kernel \w+ the solution|Your solution is okay!|uncaught exception.*)", log)
    print(f"  verdict: {'; '.join(verdict) or 'none (see the log)'}")
    span = rd(f"{name}.span").split()
    smp = [l.split() for l in rd(f"{name}-ps.log").splitlines() if len(l.split()) == 4]
    if not (span and smp):
        continue
    k0, k1 = map(float, span)
    seg = {}
    for t, pid, rss, _ in smp:
        if pid != "-":
            a = seg.setdefault(pid, [float(t), float(t), 0])
            a[1] = float(t)
            a[2] = max(a[2], int(rss))
    exp = sorted(seg.values())
    crss = max((int(c) for *_, c in smp if c != "-"), default=0)
    for i, (a, b, r) in enumerate(exp, 1):
        print(f"  lean4export {i}: {a - k0:.0f}–{b - k0:.0f} s ({b - a:.0f} s), max RSS {r / 2 ** 20:.2f} GiB")
    if len(exp) >= 2:
        print(f"  after the last export (parse both, compare, axioms, kernel replay): {k1 - exp[-1][1]:.0f} s; "
              f"comparator max RSS {crss / 2 ** 20:.2f} GiB")
        adj = (k1 - k0) - (exp[0][1] - exp[0][0])
        print(f"  without export 1 (the real challenge's export is a few constants): {adj:.0f} s; "
              f"margin 600/that {600 / adj:.2f}x")

rows = re.findall(r"\[\d+/\d+\] Built (\S+) \(([\d.]+)(m?s)\)", rd("build.log"))
fr = sorted(((float(v) / (1000 if u == "ms" else 1), m) for m, v, u in rows if m.startswith("FR") or m == "Solution"), reverse=True)
if fr:
    other = [m for m, _, _ in rows if not m.startswith("FR")]
    print(f"build: {len(fr)} FR modules built, sum of their job times {sum(t for t, _ in fr):.0f} s; "
          f"{len(other)} other modules built ({', '.join(other[:5])}{' …' if len(other) > 5 else ''})")
    print("top 20 FR modules by build job time (s; jobs run 4 at a time):")
    for t, m in fr[:20]:
        print(f"  {t:7.1f}  {m}")

for tsv in sorted(glob.glob(os.path.join(out, "kreplay-*.tsv"))):
    rows = [l.rstrip("\n").split("\t") for l in open(tsv) if l.count("\t") == 2]
    by, cnt = collections.Counter(), collections.Counter()
    for t, m, n in rows:
        by[m] += int(t) / 1e9
        cnt[m] += 1
    tot = sum(by.values())
    frs = sum(v for k, v in by.items() if k.startswith("FR"))
    print(f"{os.path.basename(tsv)}: {len(rows)} declarations, kernel {tot:.1f} s (FR modules {frs:.1f} s, "
          f"others {tot - frs:.1f} s)")
    print("  top 20 modules by kernel time (s, declarations):")
    for m, v in by.most_common(20):
        print(f"  {v:7.1f} {cnt[m]:6d}  {m}")
    print("  top 15 declarations:")
    for t, m, n in sorted(rows, key=lambda r: -int(r[0]))[:15]:
        print(f"  {int(t) / 1e9:7.2f}  {n}  ({m})")
