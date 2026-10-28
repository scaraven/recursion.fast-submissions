-- Dev-only (S-E4), outside the entry: times the node's `evalM` on the real plan (both slots of
-- `planOf (Impl.finC pending)`): the flat `TEval.evalMT` against S-E3's generic `nodeVal`.
import FRVerifierImpl

open FR RecursionFast Circ

def ms (t0 t1 : ℕ) : String := s!"{(t1 - t0) / 1000000}.{((t1 - t0) / 10000) % 100} ms"
def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407
def randF (s : UInt64) : F := let a := lcg (s ^^^ 0x5555); ⟨⟨a⟩, ⟨lcg a⟩⟩
def randAF (seed : UInt64) (n : Nat) : Array F := (Array.range n).map fun i => randF (seed * 7919 + i.toUInt64)

def fins : Finals := Impl.finC pending

def main (args : List String) : IO UInt32 := do
  let reps := (args.head? >>= String.toNat?).getD 5
  let t0 ← IO.monoNanosNow
  let pl := TEval.planOf fins
  IO.println s!"plan: slot0 skeleton groups {pl.fs0.sk.length}, insts {pl.fs0.insts.length}; slot1 insts {pl.fs1.insts.length}; keys {pl.tp.length}"
  let t1 ← IO.monoNanosNow
  IO.println s!"planOf {ms t0 t1}"; (← IO.getStdout).flush
  if args.contains "parts" then
    let τ := randAF 100 21; let σ := randAF 200 23
    let t := fun l => τ.getD l 0; let u := fun l => σ.getD l 0
    let a0 ← IO.monoNanosNow
    let tlo := TEval.loTab 11 t; let thi := TEval.loTab 10 fun l => t (11 + l)
    let slo := TEval.loTab 12 u; let shi := TEval.loTab 11 fun l => u (12 + l)
    IO.println s!"tables {tlo.size + thi.size + slo.size + shi.size}"
    let a1 ← IO.monoNanosNow
    IO.println s!"tables {ms a0 a1}"
    for s in [TEval.Mat.a, .b, .c] do
      let b0 ← IO.monoNanosNow
      let v ← IO.lazyPure fun _ => TEval.growsVal s tlo thi slo shi pl.fs0.sk
      let b1 ← IO.monoNanosNow
      let c ← IO.lazyPure fun _ => TEval.pcache s t u pl.tp
      IO.println s!"  cache {c.length} {(c.map fun p => p.2.it.length).sum}"
      let b2 ← IO.monoNanosNow
      let hv := pl.fs0.insts.map (TEval.ghv t u)
      IO.println s!"  hv {hv.length}"
      let b3 ← IO.monoNanosNow
      let e1 := TEval.glVal slo shi pl.fs0.one
      let w ← IO.lazyPure fun _ => TEval.sumL (fun gh => TEval.ginstVal s tlo thi slo shi (TEval.pfind s t u c gh.1.key) e1 gh.2 gh.1) (pl.fs0.insts.zip hv)
      let b4 ← IO.monoNanosNow
      IO.println s!"matrix: skeleton slot0 {ms b0 b1}, pcache {ms b1 b2}, hv {ms b2 b3}, instances slot0 {ms b3 b4}  [{v.c₀.val} {w.c₀.val}]"
      (← IO.getStdout).flush
    -- entries per matrix in skeleton
    let ents := pl.fs0.sk.foldl (fun n h => n + h.2.foldl (fun n r => n + (r.a.foldl (fun n g => n + g.2.length) 0) + (r.b.foldl (fun n g => n + g.2.length) 0) + (r.c.foldl (fun n g => n + g.2.length) 0)) 0) 0
    let grps := pl.fs0.sk.foldl (fun n h => n + h.2.foldl (fun n r => n + r.a.length + r.b.length + r.c.length) 0) 0
    let rows := pl.fs0.sk.foldl (fun n h => n + h.2.length) 0
    let ins := pl.fs0.insts.foldl (fun n g => n + g.ins.size) 0
    let insE := pl.fs0.insts.foldl (fun n g => n + g.ins.foldl (fun n f => n + f.foldl (fun n h => n + h.2.length) 0) 0) 0
    let al := pl.fs0.insts.foldl (fun n g => if g.al then n + 1 else n) 0
    IO.println s!"slot0 skeleton: rows {rows}, groups {grps}, entries {ents}; instances aligned {al}, inputs {ins}, input entries {insE}"
  let mut ts : Array Nat := #[]
  for i in [0:reps] do
    let τ := randAF (100 + i.toUInt64) 21; let σ := randAF (200 + i.toUInt64) 23
    let a ← IO.monoNanosNow
    let r ← IO.lazyPure fun _ => TEval.evalMT pl τ σ
    let b ← IO.monoNanosNow
    ts := ts.push (b - a)
    IO.println s!"evalMT (flat) rep {i}: {ms a b}  [{r.1.c₀.val} {r.2.1.c₀.val} {r.2.2.c₀.val}]"; (← IO.getStdout).flush
    if i == 0 && args.contains "check" then
      let t := fun l => τ.getD l 0; let u := fun l => σ.getD l 0
      let c ← IO.monoNanosNow
      let g := (TEval.nodeVal (RingHom.id F) .a t u pl, TEval.nodeVal (RingHom.id F) .b t u pl, TEval.nodeVal (RingHom.id F) .c t u pl)
      let d ← IO.monoNanosNow
      IO.println s!"nodeVal (S-E3 generic): {ms c d}, equal {g == r}"; (← IO.getStdout).flush
  let s := ts.qsort (· < ·)
  IO.println s!"evalMT best {ms 0 s[0]!}, median {ms 0 s[s.size / 2]!} over {reps}"
  return 0
