#!/usr/bin/env python3
"""Make LLVM (rustc) assembly acceptable to GNU as and free of debug info / host paths.

  sanitize-asm.py IN.s OUT.s

* drops DWARF line directives (`.file N ...`, `.loc ...`) and every line inside a `.debug_*` section
  (LLVM 23 emits DWARF-5 `.file N "dir" "file"` forms GNU as rejects, and they carry absolute
  `/rustc/<hash>` and host paths);
* rewrites `.prefalign A, .Lend, nop` (LLVM 23, unknown to GNU as) to `.p2align A` (in case
  `-C llvm-args=-align-all-functions=4` was not given);
* fails if a `.incbin` or `.include` directive remains.
"""
import re, sys

SECTION_SWITCH = re.compile(r'^\s*\.(section|text|data|bss|pushsection|popsection|previous)\b')
src, dst = sys.argv[1], sys.argv[2]
out, stack, cur, prev = [], [], "text", "text"

def name_of(line):
    m = re.match(r'^\s*\.(section|pushsection)\s+("?)([^",\s]+)', line)
    if m:
        return m.group(3)
    m = re.match(r'^\s*\.(text|data|bss)\b', line)
    return "." + m.group(1)

dropped = 0
for line in open(src, encoding="utf-8"):
    m = SECTION_SWITCH.match(line)
    if m:
        kind = m.group(1)
        if kind == "pushsection":
            stack.append(cur); prev, cur = cur, name_of(line)
        elif kind == "popsection":
            prev, cur = cur, stack.pop()
        elif kind == "previous":
            prev, cur = cur, prev
        else:
            prev, cur = cur, name_of(line)
        if cur.startswith(".debug_") or (kind in ("popsection", "previous") and False):
            dropped += 1
            continue
        out.append(line)
        continue
    if cur.startswith(".debug_"):
        dropped += 1
        continue
    s = line.lstrip()
    if re.match(r'\.file\s+\d', s) or re.match(r'\.loc\b', s) or s.startswith('.loc_mark_labels'):
        dropped += 1
        continue
    m = re.match(r'(\s*)\.prefalign\s+(\d+)\s*,.*$', line)
    if m:
        line = f"{m.group(1)}.p2align\t{m.group(2)}\n"
    if re.match(r'\.(incbin|include)\b', s):
        sys.exit(f"sanitize-asm: forbidden directive: {s.strip()}")
    out.append(line)
open(dst, "w", encoding="utf-8").write("".join(out))
print(f"sanitize-asm: {dropped} debug lines dropped", file=sys.stderr)
