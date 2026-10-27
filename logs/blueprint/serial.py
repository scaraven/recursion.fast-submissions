# The serial build path of flock-recursive (BLUEPRINT §7; S-0, kept current from S-0 on).
#   python3 -I logs/blueprint/serial.py [--rate SEC_PER_KLOC]
# Modules that exist in submissions/flock-recursive/lean are read: their FR imports and their code
# lines (the core's loc.py rule: non-blank, non-comment). Planned modules come from the table below
# (BLUEPRINT §7, revision 3.4: lines and FR imports). The serial path is the longest import chain
# weighted by code lines; its time is an **estimate** at RATE CPU-seconds per kLoC (default 30, the
# blueprint's figure), to be replaced by S-E's VM measurement (FR-R4').
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SRC = os.path.join(ROOT, "submissions", "flock-recursive", "lean")
RATE = float(sys.argv[sys.argv.index("--rate") + 1]) if "--rate" in sys.argv else 30.0

# Planned modules: name -> (code lines, [FR imports]). A group of the §7 table is split into a chain.
PLAN = {
    "FRFieldDefs": (300, ["FRFieldBase"]),
    "FRPubTarget": (250, ["FRMLE"]),
    "FRRSEval": (400, ["FRRS"]),
    "FRProximityFold": (700, ["FRProximityLine"]),
    "FROracle": (120, []), "FRQueries": (120, ["FROracle"]),
    "FRTranscript": (350, ["FRTranscriptDefs", "FRVIR"]),
    "FRLog": (800, ["FRMerkle"]),
    "FRBlockChain": (430, ["FRBlockLayout"]), "FRBlockStream": (440, ["FRBlockChain"]),
    "FRLeafCircuit": (1200, ["FRBlockStream"]),
    "FRVIRCompile": (1200, ["FRVIR", "FRSpartan", "FRBlake2sWalk"]),
    "FRVIRMux": (600, ["FRVIRCompile"]),
    "FRVIREval": (1100, ["FRVIRCompile", "FRRSEval", "FRRingSwitch"]),
    "FRWots": (700, ["FRVIRMux", "FRBlockStream"]),
    "FRNodeLayout": (400, ["FRWots", "FRLeafCircuit", "FRPubTarget", "FRShift"]),
    "FRNodeCircuit": (1200, ["FRNodeLayout"]),
    "FRVerifier": (800, ["FRVIRFinals", "FRVIREval", "FRFormat"]),
    "FRSoundnessDefs": (800, ["FRLog", "FRProximityFold", "FRVerifier"]),
    "FRSoundnessStepA": (1100, ["FRSoundnessDefs", "FRSkip", "FRSpartan", "FRRingSwitch",
                                "FRPubTarget", "FRShift"]),
    "FRSoundnessStepB": (1100, ["FRSoundnessStepA"]),
    "FRSoundnessLigerito": (1000, ["FRSoundnessDefs", "FRProximityFold", "FRMerkle"]),
    "FRSoundnessFinal": (1200, ["FRSoundnessStepB", "FRSoundnessLigerito", "FRNodeCircuit",
                                "FRLeafCircuit"]),
    "FRKState": (200, ["FRSoundnessFinal"]), "FRCompleteness": (150, ["FRVerifier"]),
    "FRXField": (900, ["FRXDsl", "FRField256"]),
    "FRXLog": (800, ["FRXField", "FRFormat", "FRTranscriptDefs"]),
    "FRXDecodeA": (800, ["FRXLog"]), "FRXDecodeB": (800, ["FRXDecodeA"]),
    "FRXProg": (800, ["FRXDecodeB"]),
    "FRXComputes": (900, ["FRXProg"]), "FRXSpec": (900, ["FRXComputes", "FRSoundnessLigerito"]),
    "FRSubmission": (600, ["FRKState", "FRCompleteness", "FRXSpec"]),
    "FRFinal": (500, ["FRSubmission"]), "FRControls": (400, ["FRFinal"]),
    "Solution": (100, ["FRControls"]),
}


def code_lines(path):
    """Non-blank, non-comment lines (nested block comments and line comments removed)."""
    src = open(path, encoding="utf-8").read()
    out, depth, i = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if not depth:
            out.append(src[i])
        i += 1
    lines = "".join(out).split("\n")
    return sum(1 for l in lines if l.strip() and not l.strip().startswith("--"))


def actual():
    mods = {}
    for f in sorted(os.listdir(SRC)):
        if f.endswith(".lean"):
            name = f[:-5]
            text = open(os.path.join(SRC, f), encoding="utf-8").read()
            imps = [m for m in re.findall(r"^import\s+(\S+)", text, re.M) if m.startswith("FR")]
            mods[name] = (code_lines(os.path.join(SRC, f)), imps, "actual")
    return mods


def main():
    mods = actual()
    for k, (n, imps) in PLAN.items():
        if k not in mods:
            mods[k] = (n, imps, "plan")
    memo = {}

    def longest(m):
        if m in memo:
            return memo[m]
        n, imps, _ = mods.get(m, (0, [], "missing"))
        best = max((longest(i) for i in imps if i in mods), default=(0, []))
        memo[m] = (best[0] + n, best[1] + [m])
        return memo[m]

    total = sum(v[0] for v in mods.values())
    act = sum(v[0] for v in mods.values() if v[2] == "actual")
    L, path = longest("Solution")
    print(f"modules {len(mods)} ({sum(1 for v in mods.values() if v[2] == 'actual')} actual); "
          f"code lines {total} ({act} actual, {total - act} planned)")
    print(f"serial path {L} lines, {L * RATE / 1000:.0f} s at {RATE:g} CPU-s/kLoC (estimate):")
    print("  " + " -> ".join(f"{m}({mods[m][0]}{'' if mods[m][2] == 'actual' else 'p'})" for m in path))
    # the S-0 modules' own chain
    for m in ("FRVIRSpec", "FRVerifier"):
        l, p = longest(m)
        print(f"to {m}: {l} lines: " + " -> ".join(p))


main()
