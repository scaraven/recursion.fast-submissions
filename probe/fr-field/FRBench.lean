/-
  S-A: compiled product times of the entry's fields (`FR.B64`, `FR.F`, `FR.K`), the entry's own
  modules imported as built, so the measured code is the certified code.

    frbench REPS N   -- prints `op kind median_ns min_ns checksum` per operation

  Inputs come from a splitmix64 stream seeded from the clock; each result is folded into a printed
  checksum, so nothing is evaluated at compile time or dropped. "lat" chains `x := x * y`; "thr"
  runs four independent chains. Same method as phase 0's `probe/lean-field/Main.lean`.
-/
import FRField256

open FR

@[inline] def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (s, z ^^^ (z >>> 31))

def latB : Nat → B64 → B64 → B64
  | 0, x, _ => x
  | n + 1, x, y => latB n (x * y) y

def latF : Nat → F → F → F
  | 0, x, _ => x
  | n + 1, x, y => latF n (x * y) y

def latK : Nat → K → K → K
  | 0, x, _ => x
  | n + 1, x, y => latK n (x * y) y

def latFsq : Nat → F → F
  | 0, x => x
  | n + 1, x => latFsq n (F.sq x)

def latFinv : Nat → F → F → F
  | 0, x, _ => x
  | n + 1, x, y => latFinv n (x⁻¹ + y) y

def thrF : Nat → F → F → F → F → F → F
  | 0, a, b, c, d, _ => a + b + c + d
  | n + 1, a, b, c, d, y => thrF n (a * y) (b * y) (c * y) (d * y) y

def thrK : Nat → K → K → K → K → K → K
  | 0, a, b, c, d, _ => a + b + c + d
  | n + 1, a, b, c, d, y => thrK n (a * y) (b * y) (c * y) (d * y) y

def thrB : Nat → B64 → B64 → B64 → B64 → B64 → B64
  | 0, a, b, c, d, _ => a + b + c + d
  | n + 1, a, b, c, d, y => thrB n (a * y) (b * y) (c * y) (d * y) y

def median (xs : Array Nat) : Nat := (xs.qsort (· < ·))[xs.size / 2]!

def minA (xs : Array Nat) : Nat := xs.foldl min xs[0]!

/-- Run `f` `reps` times; `ops` operations per run. -/
def runBench (name kind : String) (reps ops : Nat) (f : Unit → IO UInt64) : IO Unit := do
  let mut ts : Array Nat := #[]
  let mut ck : UInt64 := 0
  for _ in [0:reps] do
    let t0 ← IO.monoNanosNow
    let r ← f ()
    let t1 ← IO.monoNanosNow
    ck := ck ^^^ r
    ts := ts.push (t1 - t0)
  let med := (median ts).toFloat / ops.toFloat
  let mn := (minA ts).toFloat / ops.toFloat
  IO.println s!"{name} {kind} {med} {mn} {ck}"

def main (args : List String) : IO Unit := do
  let reps := (args.getD 0 "7").toNat!
  let n := (args.getD 1 "1000000").toNat!
  let seed ← IO.monoNanosNow
  let (s, w0) := splitmix seed.toUInt64
  let (s, w1) := splitmix s
  let (s, w2) := splitmix s
  let (s, w3) := splitmix s
  let (s, w4) := splitmix s
  let (s, w5) := splitmix s
  let (s, w6) := splitmix s
  let (_, w7) := splitmix s
  let bx : B64 := ⟨w0⟩
  let by_ : B64 := ⟨w1⟩
  let fx : F := ⟨⟨w0⟩, ⟨w1⟩⟩
  let fy : F := ⟨⟨w2⟩, ⟨w3⟩⟩
  let kx : K := ⟨⟨⟨w0⟩, ⟨w1⟩⟩, ⟨⟨w2⟩, ⟨w3⟩⟩⟩
  let ky : K := ⟨⟨⟨w4⟩, ⟨w5⟩⟩, ⟨⟨w6⟩, ⟨w7⟩⟩⟩
  let fsum (a : F) : UInt64 := a.c₀.val ^^^ a.c₁.val
  let ksum (a : K) : UInt64 := fsum a.f₀ ^^^ fsum a.f₁
  runBench "B64.mul" "lat" reps n fun _ => pure (latB n bx by_).val
  runBench "B64.mul" "thr" reps (4 * n) fun _ => pure (thrB n bx by_ (bx * by_) (bx + by_) by_).val
  runBench "F.mul" "lat" reps n fun _ => pure (fsum (latF n fx fy))
  runBench "F.mul" "thr" reps (4 * n) fun _ => pure (fsum (thrF n fx fy (fx * fy) (fx + fy) fy))
  runBench "F.sq" "lat" reps n fun _ => pure (fsum (latFsq n fx))
  runBench "K.mul" "lat" reps n fun _ => pure (ksum (latK n kx ky))
  runBench "K.mul" "thr" reps (4 * n) fun _ => pure (ksum (thrK n kx ky (kx * ky) (kx + ky) ky))
  let m := n / 100
  runBench "F.inv" "lat" reps m fun _ => pure (fsum (latFinv m fx fy))
