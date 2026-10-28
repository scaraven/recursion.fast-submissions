"""H-cert: the target lists without the entry's controls (what `certified` does not use).
  python3 -I filter-controls.py NAMEDIR OUTDIR
A target is a control if a namespace component ends in `Controls`, or its last component starts with
`ctrl`/`toy` or contains `Ctrl`/`_kat`/`Controls`. (Modules named *Controls* declare only such names.)"""
import os, re, sys

src, dst = sys.argv[1:]
os.makedirs(dst, exist_ok=True)
ctl = lambda n: (any(c.endswith("Controls") for c in n.split(".")[:-1])
                 or re.match(r"(ctrl|toy)", n.split(".")[-1]) or re.search(r"Ctrl|_kat|Controls", n.split(".")[-1]))
for f in ("theorems.txt", "definitions.txt"):
    names = [l.strip() for l in open(os.path.join(src, f)) if l.strip()]
    keep = [n for n in names if not ctl(n)]
    open(os.path.join(dst, f), "w").write("\n".join(keep) + "\n")
    print(f"{f}: {len(keep)} of {len(names)} kept ({len(names) - len(keep)} controls dropped)")
