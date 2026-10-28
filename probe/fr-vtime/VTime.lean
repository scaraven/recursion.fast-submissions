-- Dev-only timing probe (S-F2), outside the entry: a compiled `main`, no elaboration-time code.
-- `vtime v K` times the verifier `Vwith (implC …) finC` on a synthetic SNARK proof of kind `K`
-- (`L`/`P`/`N`): random proof bytes of `piSize`, an oracle answering every query with a fresh
-- pseudo-random digest; the trace it records is then replayed with `runSeq` (the `acc` path).
-- `vtime ops` times the heavy ops one by one on random operands.
import FRVerifierImpl

open FR RecursionFast

/-- A 64-bit LCG step. -/
def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def randBytes (seed : UInt64) (n : ℕ) : ByteArray := Id.run do
  let mut s := seed
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    s := lcg s
    b := b.push (s >>> 56).toUInt8
  return b

def randDigest (seed : UInt64) : Digest :=
  let b := randBytes seed 32
  Vector.ofFn fun i : Fin 32 => b.get! i.val

def randF (seed : UInt64) : F := F.ofBytes (Vector.ofFn fun i : Fin 16 => (randBytes seed 16).get! i.val)
def randK (seed : UInt64) : K := K.ofBytes (Vector.ofFn fun i : Fin 32 => (randBytes seed 32).get! i.val)
def randAF (seed : UInt64) (n : ℕ) : Array F := (Array.range n).map fun i => randF (seed + 7919 * i.toUInt64)
def randAK (seed : UInt64) (n : ℕ) : Array K := (Array.range n).map fun i => randK (seed + 7919 * i.toUInt64)

/-- The finals: S-0's, S-F's, S-G's `finP`; `finPf` pending (S-G1d). -/
def finC : Finals := Impl.finC pending

def implP : OpImpl := Impl.implC finC [] 0

def Vp (vk c : Digest) (π : Proof) : OProg Bool := Vwith implP finC vk c π

/-- Run against a pseudo-random oracle, recording the trace. -/
partial def collect (p : OProg Bool) (s : UInt64) (acc : Array (ByteArray × Digest)) :
    Bool × Array (ByteArray × Digest) :=
  match p with
  | .ret b => (b, acc)
  | .query q k => let a := randDigest s; collect (k a) (lcg s) (acc.push (q, a))

def ms (t0 t1 : ℕ) : String := s!"{(t1 - t0) / 1000000}.{((t1 - t0) / 10000) % 100} ms"

def proofOf (κ : Kind) : Proof :=
  let b := randBytes 12345 piSize
  b.set! 0 κ.byte

def timeV (κ : Kind) (reps : ℕ) : IO Unit := do
  let vk := randDigest 1; let c := randDigest 2; let π := proofOf κ
  IO.println s!"kind {repr κ}: |π| = {π.size}, kindOf snark: {match kindOf π with | .snark _ => true | _ => false}"
  let t0 ← IO.monoNanosNow
  let (b, tr) ← IO.lazyPure fun _ => collect (Vp vk c π) 99 #[]
  let t1 ← IO.monoNanosNow
  IO.println s!"collect (oracle run): {ms t0 t1}, result {b}, |tr| = {tr.size}, trace bytes = {(tr.foldl (fun a e => a + e.1.size + 32) 0)}"
  (← IO.getStdout).flush
  let trl := tr.toList
  let mut ts : Array ℕ := #[]
  for i in [0:reps] do
    let t2 ← IO.monoNanosNow
    let r ← IO.lazyPure fun _ => (Vp vk c π).runSeq trl
    let t3 ← IO.monoNanosNow
    ts := ts.push (t3 - t2)
    IO.println s!"runSeq rep {i}: {ms t2 t3} (result {r})"
    (← IO.getStdout).flush
  let srt := ts.qsort (· < ·)
  IO.println s!"runSeq best {ms 0 srt[0]!}, median {ms 0 srt[srt.size / 2]!} over {reps}"
  let t4 ← IO.monoNanosNow
  let d ← IO.lazyPure fun _ => traceDigestF trl
  let t5 ← IO.monoNanosNow
  IO.println s!"traceDigestF: {ms t4 t5} ({d.toList.take 2})"

def timeOp (name : String) (reps : ℕ) (f : Unit → String) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut out := ""
  for _ in [0:reps] do
    out := f ()
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}: {ms t0 t1} / {reps} reps  [{out.take 16}]"
  (← IO.getStdout).flush

def hexF (x : F) : String := toString x.toBytes.toList.head!

def timeRows : IO Unit := do
  -- S-E4: the node's plan (both slots' templated compile and their flat forms), then `evalM`
  let t0 ← IO.monoNanosNow
  let pl := TEval.planOf finC
  IO.println s!"plan: {pl.fs0.insts.length} + {pl.fs1.insts.length} instances"
  let t1 ← IO.monoNanosNow
  IO.println s!"planOf {ms t0 t1}"
  timeOp "evalM (flat, TEval.evalMT)" 3 fun _ => hexF (TEval.evalMT pl (randAF 19 21) (randAF 20 23)).1

def timeOps : IO Unit := do
  let l := randF 5
  timeOp "lagrangeS" 10 fun _ => hexF (Impl.lagrangeSI (randAF 6 127) l (randAF 7 64)).1
  timeOp "eqZ" 10 fun _ => hexF ((Impl.eqZI l (randF 8)).getD 3 0)
  timeOp "rowW" 10 fun _ => hexF ((Impl.rowWI l (randAF 9 8)).getD 3 0)
  let rw := Impl.rowWI l (randAF 9 8); let cw := eqTab (randAF 10 14)
  timeOp "walkAB" 3 fun _ => hexF (Eval.walkImpl rw cw).1
  timeOp "maskRows" 3 fun _ => hexF ((maskRows (randAF 11 9) rw).getD 5 0)
  let r7 := randAF 12 7
  timeOp "phiRS x512" 1 fun _ => hexF ((List.range 512).foldl (fun a i => a + Impl.phiRSI r7 (randF i.toUInt64)) 0)
  let pts := (List.range 4).map fun j => randAK (100 + j.toUInt64) 23
  timeOp "rsWeight (4 claims, 23 coords)" 1 fun _ => toString (Impl.rsWeightI r7 pts l (randAK 13 23)).toBytes.toList.head!
  timeOp "tensorW x250 (7 coords)" 1 fun _ => toString ((List.range 250).foldl (fun a j => a + Impl.tensorWI j (randAK 14 7)) 0).toBytes.toList.head!
  timeOp "slotW" 10 fun _ => hexF (Impl.slotWI 1 (randAF 15 10) (randAF 16 10))
  timeOp "shiftTarget" 10 fun _ => hexF (Impl.shiftTargetI l (randAF 15 16) (randAF 16 10) (randAF 17 4))
  timeOp "targetS (leaf)" 10 fun _ => hexF ((Impl.targetSLeafI (randAF 18 20)).getD 3 0)

def opName : Op → String
  | .input .. => "input" | .const .. => "const" | .piField .. => "piField" | .piElem .. => "piElem"
  | .piElemK .. => "piElemK" | .piDigest .. => "piDigest" | .piDigestAt .. => "piDigestAt"
  | .mkAbsorb .. => "mkAbsorb" | .askSeed .. => "askSeed" | .askAbsorb .. => "askAbsorb"
  | .askSqueeze .. => "askSqueeze" | .askNode .. => "askNode" | .askCol .. => "askCol"
  | .chF .. => "chF" | .chK .. => "chK" | .idx .. => "idx" | .bitOf .. => "bitOf" | .shrN .. => "shrN"
  | .mulF .. => "mulF" | .addF .. => "addF" | .mulK .. => "mulK" | .addK .. => "addK"
  | .mulKF .. => "mulKF" | .invF .. => "invF" | .packF .. => "packF" | .packK .. => "packK"
  | .packFK .. => "packFK" | .getF .. => "getF" | .getK .. => "getK" | .eqTable .. => "eqTable"
  | .eqTableK .. => "eqTableK" | .dotKF .. => "dotKF" | .lagrangeS .. => "lagrangeS"
  | .targetS .. => "targetS" | .eqZ .. => "eqZ" | .tensorW .. => "tensorW" | .rsWeight .. => "rsWeight"
  | .phiRS .. => "phiRS" | .walkAB .. => "walkAB" | .kindInd .. => "kindInd"
  | .maskRows .. => "maskRows" | .evalM .. => "evalM" | .evalL .. => "evalL"
  | .shiftTarget .. => "shiftTarget" | .slotW .. => "slotW" | .kindFoldWeight .. => "kindFoldWeight"
  | .eqPt .. => "eqPt" | .rowW .. => "rowW" | .shiftEq .. => "shiftEq" | .linkW .. => "linkW"
  | .splitDigest .. => "splitDigest" | .selectHalf .. => "selectHalf" | .keep .. => "keep"
  | .hashStmt .. => "hashStmt" | .kindSel => "kindSel" | .assertEq .. => "assertEq"
  | .assertBit .. => "assertBit" | .assertZero .. => "assertZero" | .assertOneHot .. => "assertOneHot"
  | .accept => "accept"

/-- Run the op list by hand, timing each op kind. -/
def profileOps (κ : Kind) : IO Unit := do
  let out ← IO.getStdout
  let vk := randDigest 1; let c := randDigest 2; let π := proofOf κ
  let inp : Input := ⟨vk, c, π⟩
  let t0 ← IO.monoNanosNow
  let ops := (gen finC (.fixed κ)).ops
  let n := ops.length
  let t1 ← IO.monoNanosNow
  IO.println s!"gen: {n} ops in {ms t0 t1}"; out.flush
  let mut regs : Array Val := #[]
  let mut ok := true
  let mut tab : Std.HashMap String (ℕ × ℕ) := {}
  let mut s : UInt64 := 99
  let mut i := 0
  for op in ops do
    let a ← IO.monoNanosNow
    match evalOp implP κ inp regs op with
    | .vals vs o => regs := regs ++ vs.toArray; ok := ok && o
    | .ask q => regs := regs.push (.d (randDigest s)); s := lcg s; if q.size == 0 then ok := false
    let b ← IO.monoNanosNow
    let (cnt, tm) := tab.getD (opName op) (0, 0)
    tab := tab.insert (opName op) (cnt + 1, tm + (b - a))
    i := i + 1
    if i % 20000 == 0 then IO.println s!"  op {i}: total so far"; out.flush
  let t2 ← IO.monoNanosNow
  IO.println s!"run: {ms t1 t2}, flag {ok}, regs {regs.size}"
  let rows := tab.toList.mergeSort (fun x y => x.2.2 ≥ y.2.2)
  for (nm, (cnt, tm)) in rows do
    IO.println s!"  {nm}: {cnt} ops, {ms 0 tm}"

def main (args : List String) : IO Unit := do
  match args with
  | ["v", k] =>
    let κ := match k with | "L" => Kind.L32 | "P" => Kind.P30 | _ => Kind.N30
    timeV κ 9
  | ["ops"] => timeOps
  | ["rows"] => timeRows
  | ["prof", k] =>
    let κ := match k with | "L" => Kind.L32 | "P" => Kind.P30 | _ => Kind.N30
    profileOps κ
  | _ => IO.println "usage: vtime v L|P|N | vtime ops"
