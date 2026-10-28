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

/-- The full finals (revision 3.13): S-0's, S-F's, S-G's `finP` and `finPf`. -/
def finC : Finals := Impl.finC finPf

def implP : OpImpl := Impl.implC finC Layout.lRows 0

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
  IO.println s!"plan: {pl.keys.size} keys, {pl.pc0.length} + {pl.pc1.length} pieces"
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
  | .eqPt .. => "eqPt" | .rowW .. => "rowW" | .shiftEq .. => "shiftEq" | .linkWAll .. => "linkWAll" | .shiftMask .. => "shiftMask"
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


/-- S-E8 prototypes for `tensorW`. -/
def tw1 (j : ℕ) (r : Array K) : K :=
  Impl.prodTo r.size fun v => 1 - r.getD v 0 + K.smulF (Impl.wAtT v j) (r.getD v 0)

def wByte : Array (Array F) := Array.ofFn (n := 3 * FR.logNMax) fun vb =>
  let v := vb.val / 3; let b := vb.val % 3
  Array.ofFn (n := 256) fun x => FR.sumTo 8 fun i =>
    if x.val.testBit i && 8 * b + i < FR.logNMax then ((Impl.wTab.getD v #[]).getD (8 * b + i) 0) else 0

def wAtB (v j : ℕ) : F :=
  (wByte.getD (3 * v) #[]).getD (j % 256) 0 + (wByte.getD (3 * v + 1) #[]).getD (j / 256 % 256) 0 +
    (wByte.getD (3 * v + 2) #[]).getD (j / 65536 % 16) 0

def wAtB2 (v j : ℕ) : F :=
  (Impl.wByte.getD (3 * v) #[]).getD (j % 256) 0 + (Impl.wByte.getD (3 * v + 1) #[]).getD (j / 256 % 256) 0 +
    (Impl.wByte.getD (3 * v + 2) #[]).getD (j / 65536 % 256) 0

def tw3 (j : ℕ) (r : Array K) : K :=
  Impl.prodTo r.size fun v => 1 - r.getD v 0 + K.smulF (wAtB2 v j) (r.getD v 0)

def tw4 (j : ℕ) (r : Array K) : K :=
  Impl.prodTo r.size fun v => 1 - r.getD v 0 + K.smulF (Impl.wB v 0 j + Impl.wB v 1 j + Impl.wB v 2 j) (r.getD v 0)

def tw2 (j : ℕ) (r : Array K) : K :=
  Impl.prodTo r.size fun v => 1 - r.getD v 0 + K.smulF (wAtB v j) (r.getD v 0)

def timeNQ : IO Unit := do
  let ds := (List.range 7552).map fun i => (randDigest (i.toUInt64 + 5), randDigest (i.toUInt64 + 9))
  IO.println s!"check: {ds.all fun (l, r) => nodeQF 3 l r == nodeQ 3 l r}"
  timeOp "nodeQ x7552" 5 fun _ => toString (ds.foldl (fun a (l, r) => a + (nodeQ 3 l r).size) 0)
  timeOp "nodeQF x7552" 5 fun _ => toString (ds.foldl (fun a (l, r) => a + (nodeQF 3 l r).size) 0)
  let qs := ds.map fun (l, r) => (nodeQ 3 l r, nodeQF 3 l r)
  timeOp "compare x7552" 5 fun _ => toString (qs.foldl (fun a (x, y) => a + if x = y then 1 else 0) 0)
  timeOp "randDigest x7552" 5 fun _ => toString (ds.foldl (fun a (l, _) => a + (randDigest l[0].toUInt64).toArray.size) 0)

def dAt2 (q : ByteArray) (o : ℕ) : Array UInt8 := (q.extract o (o + 32)).data

def timePD : IO Unit := do
  let π := proofOf .N30
  let os := (List.range 7555).map fun i => (i * 97) % (π.size - 40)
  IO.println s!"check: {os.all fun o => (bytesAt π o 32).toArray == dAt2 π o}"
  timeOp "bytesAt 32 x7555" 5 fun _ => toString (os.foldl (fun a o => a + (bytesAt π o 32)[3].toNat) 0)
  timeOp "extract.data x7555" 5 fun _ => toString (os.foldl (fun a o => a + (dAt2 π o)[3]!.toNat) 0)
  timeOp "bytesAt 16 + F.ofBytes x7555" 5 fun _ => toString (os.foldl (fun a o => a + (F.ofBytes (bytesAt π o 16)).c₀.val.toNat % 7) 0)
  timeOp "fAt x7555" 5 fun _ => toString (os.foldl (fun a o => a + (fAt π o).c₀.val.toNat % 7) 0)
  let rs := randAF 3 14
  timeOp "eqTab 14 F" 5 fun _ => hexF ((eqTab rs).getD 5 0)

/-- S-E8 item 7: the shared `Â₀(τ_lo, σ_lo)`, `B̂₀(τ_lo, σ_lo)` of the child's walk template: two
`eq` tables over the block's 14 row / 14 column bits, then one fused walk. -/
def timeCW : IO Unit := do
  for (sd, sd2) in [(31, 37), (41, 43), (47, 53)] do
    let t := randAF sd 14; let s := randAF sd2 14
    let t0 ← IO.monoNanosNow
    let et ← IO.lazyPure fun _ => eqTab t
    let t1 ← IO.monoNanosNow
    let es ← IO.lazyPure fun _ => eqTab s
    let t2 ← IO.monoNanosNow
    let w ← IO.lazyPure fun _ => Eval.walkImpl et es
    let t3 ← IO.monoNanosNow
    IO.println s!"eqTab τ_lo {ms t0 t1}, eqTab σ_lo {ms t1 t2}, walkImpl (A₀, B₀ fused) {ms t2 t3}, total {ms t0 t3} [{hexF w.1}]"
    (← IO.getStdout).flush
  -- V's own walkAB inputs for comparison (rowW′ = maskRows of rowW, colW = eqTab r_k)
  let rw := maskRows (randAF 11 9) (Impl.rowWI (randF 5) (randAF 9 8)); let cw := eqTab (randAF 10 14)
  timeOp "walkImpl at V's own (rowW′, colW)" 5 fun _ => hexF (Eval.walkImpl rw cw).1
  let et := eqTab (randAF 31 14); let es := eqTab (randAF 37 14)
  timeOp "walkImpl at (eq τ_lo, eq σ_lo)" 5 fun _ => hexF (Eval.walkImpl et es).1
  timeOp "eqTab 14 (F)" 5 fun _ => hexF ((eqTab (randAF 31 14)).getD 5 0)

def timeTW : IO Unit := do
  let r := randAK 14 7
  let js := (List.range 1627).map fun i => (lcg (i.toUInt64 + 3)).toNat % (2 ^ 20)
  IO.println s!"check: {js.all fun j => tw1 j r == Impl.tensorWI j r} {js.all fun j => tw2 j r == Impl.tensorWI j r} {(wByte.size)}"
  timeOp "tensorWI x1627" 5 fun _ => toString (js.foldl (fun a j => a + Impl.tensorWI j r) 0).toBytes.toList.head!
  timeOp "tw1 (smulF) x1627" 5 fun _ => toString (js.foldl (fun a j => a + tw1 j r) 0).toBytes.toList.head!
  timeOp "tw2 (smulF, byte tables) x1627" 5 fun _ => toString (js.foldl (fun a j => a + tw2 j r) 0).toBytes.toList.head!
  timeOp "tw3 (Impl.wByte, literals) x1627" 5 fun _ => toString (js.foldl (fun a j => a + tw3 j r) 0).toBytes.toList.head!
  timeOp "tw4 (Impl.wB) x1627" 5 fun _ => toString (js.foldl (fun a j => a + tw4 j r) 0).toBytes.toList.head!
  for n in [7, 13, 20] do
    let r := randAK 14 n
    timeOp s!"Impl.tensorWI n={n} x1627" 5 fun _ => toString (js.foldl (fun a j => a + Impl.tensorWI j r) 0).toBytes.toList.head!
    timeOp s!"Impl.tensorWF n={n} x1627" 5 fun _ => toString (js.foldl (fun a j => a + Impl.tensorWF j r) 0).toBytes.toList.head!
  timeOp "wAtT x1627x7" 5 fun _ => hexF (js.foldl (fun a j => a + (List.range 7).foldl (fun b v => b + Impl.wAtT v j) 0) 0)

def main (args : List String) : IO Unit := do
  match args with
  | ["v", k] =>
    let κ := match k with | "L" => Kind.L32 | "P" => Kind.P30 | _ => Kind.N30
    timeV κ 9
  | ["v", k, n] =>
    let κ := match k with | "L" => Kind.L32 | "P" => Kind.P30 | _ => Kind.N30
    timeV κ n.toNat!
  | ["ops"] => timeOps
  | ["tw"] => timeTW
  | ["nq"] => timeNQ
  | ["cw"] => timeCW
  | ["pd"] => timePD
  | ["rows"] => timeRows
  | ["prof", k] =>
    let κ := match k with | "L" => Kind.L32 | "P" => Kind.P30 | _ => Kind.N30
    profileOps κ
  | _ => IO.println "usage: vtime v L|P|N | vtime ops"
