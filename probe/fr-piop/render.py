#!/usr/bin/env python3
"""Render FRSkip.template with the literals of gen_skip_two.out into the entry's FRSkip.lean."""
import sys
o=open("gen_skip_two.out").read().splitlines()
def grab(tag):
    for l in o:
        if l.startswith("-- "+tag+" "): return l[len(tag)+4:]
z=grab("zeta"); g=grab("g"); gl=grab("gl"); rho=grab("rho")
i=o.index("-- w"); w=[x.strip().rstrip(",") for x in o[i+1:i+129]]
j=o.index("-- Ninv"); n=[x.strip().rstrip(",") for x in o[j+1:j+129]]
g="".join(f"⟨{x.strip()}⟩, " for x in g.split(","))[:-2]
def lst(xs): return "\n  " + ",\n  ".join(xs)
def wrap(s, ind="  "): return ("⟩⟩,\n"+ind).join(s.split("⟩⟩, "))
t=open("FRSkip.template").read()
t=t.replace("@@ZETA@@",z).replace("@@G@@","\n  "+g.replace("⟩, ","⟩,\n  ")).replace("@@GL@@","\n  "+wrap(gl)).replace("@@RHO@@","\n  "+wrap(rho))
t=t.replace("@@W@@",lst(w)).replace("@@NINV@@",lst(n))
open(sys.argv[1],"w").write(t)
