-- Dev-only (S-E4): the generic gadget program of FRBlake2sGeneric copied with `@[specialize]` on
-- every definition, to time the walk when the compiler specialises it to `walkOps`.
import FRBlake2sWalk
import FRField128
open FR RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit

namespace FR
namespace GOps2

variable {m : ℕ} {α S : Type} (o : GOps m α S)

/-- The product gate at the next position. -/
@[specialize] def mul (a b : α) : GB S α :=
  modifyGet fun s ↦ (o.res (pos s.next) a b, ⟨s.next + 1, o.upd s.acc (pos s.next) a b⟩)

/-- `xorW`. -/
@[specialize] def xorW (x y : Vector α 32) : Vector α 32 := Vector.ofFn fun i ↦ o.xor x[i] y[i]

/-- `rotrW`. -/
@[specialize] def rotrW (w : Vector α 32) (n : ℕ) : Vector α 32 :=
  Vector.ofFn fun i ↦ w[(i.val + n) % 32]'(Nat.mod_lt _ (by decide))

/-- `litW`. -/
@[specialize] def litW (cpos : Pos m) (c : UInt32) : Vector α 32 :=
  Vector.ofFn fun i ↦ if c.toNat.testBit i then o.var cpos else o.zero

/-- `inW`. -/
@[specialize] def inW (b : ℕ) : Vector α 32 := Vector.ofFn fun i ↦ o.var (pos (b + i))

/-- `addCarries`. -/
@[specialize] def addCarries (x y : Vector α 32) : (n : ℕ) → α → GB S (List α)
  | 0, c => pure [c]
  | n + 1, c => do
    let i := 30 - n
    let g ← o.mul (o.xor (x[i]'(by omega)) c) (o.xor (y[i]'(by omega)) c)
    let rest ← addCarries x y n (o.xor c g)
    pure (c :: rest)

/-- `sumW`. -/
@[specialize] def sumW (p q : Vector α 32) (cs : List α) : Vector α 32 :=
  Vector.ofFn fun i ↦ o.xor (o.xor p[i] q[i]) (cs.getD i o.zero)

/-- `addW`. -/
@[specialize] def addW (x y : Vector α 32) : GB S (Vector α 32) := o.sumW x y <$> o.addCarries x y 31 o.zero

/-- `majorities`. -/
@[specialize] def majorities (x y z : Vector α 32) : (n : ℕ) → GB S (List α)
  | 0 => pure []
  | n + 1 => do
    let i := 30 - n
    let g ← o.mul (o.xor (x[i]'(by omega)) (z[i]'(by omega)))
      (o.xor (y[i]'(by omega)) (z[i]'(by omega)))
    let rest ← majorities x y z n
    pure (o.xor g (z[i]'(by omega)) :: rest)

/-- `rippleCarries`. -/
@[specialize] def rippleCarries (p q : Vector α 32) : (n : ℕ) → α → GB S (List α)
  | 0, c => pure [c]
  | n + 1, c => do
    let i := 30 - n
    if 1 ≤ i then
      let g ← o.mul (o.xor (p[i]'(by omega)) c) (o.xor (q[i]'(by omega)) c)
      let rest ← rippleCarries p q n (o.xor c g)
      pure (c :: rest)
    else
      let rest ← rippleCarries p q n c
      pure (c :: rest)

/-- `xor3W`. -/
@[specialize] def xor3W (x y z : Vector α 32) : Vector α 32 :=
  Vector.ofFn fun i ↦ o.xor (o.xor x[i] y[i]) z[i]

/-- `shiftW`. -/
@[specialize] def shiftW (ms : List α) : Vector α 32 :=
  Vector.ofFn fun i ↦ if i.val = 0 then o.zero else ms.getD (i.val - 1) o.zero

/-- `add3W`. -/
@[specialize] def add3W (x y z : Vector α 32) : GB S (Vector α 32) :=
  o.majorities x y z 31 >>= fun ms ↦
    o.sumW (o.xor3W x y z) (o.shiftW ms) <$> o.rippleCarries (o.xor3W x y z) (o.shiftW ms) 31 o.zero

/-- `gW`. -/
@[specialize] def gW (v : Vector (Vector α 32) 16) (a b c d : Fin 16) (mx my : Vector α 32) :
    GB S (Vector (Vector α 32) 16) := do
  let a1 ← o.add3W v[a] v[b] mx
  let d1 := GOps.rotrW (o.xorW v[d] a1) 16
  let c1 ← o.addW v[c] d1
  let b1 := GOps.rotrW (o.xorW v[b] c1) 12
  let a2 ← o.add3W a1 b1 my
  let d2 := GOps.rotrW (o.xorW d1 a2) 8
  let c2 ← o.addW c1 d2
  let b2 := GOps.rotrW (o.xorW b1 c2) 7
  pure ((((v.set a a2).set b b2).set c c2).set d d2)

/-- `roundW`. -/
@[specialize] def roundW (v m' : Vector (Vector α 32) 16) (s : Vector (Fin 16) 16) :
    GB S (Vector (Vector α 32) 16) := do
  let v ← o.gW v 0 4 8 12 m'[s[0]] m'[s[1]]
  let v ← o.gW v 1 5 9 13 m'[s[2]] m'[s[3]]
  let v ← o.gW v 2 6 10 14 m'[s[4]] m'[s[5]]
  let v ← o.gW v 3 7 11 15 m'[s[6]] m'[s[7]]
  let v ← o.gW v 0 5 10 15 m'[s[8]] m'[s[9]]
  let v ← o.gW v 1 6 11 12 m'[s[10]] m'[s[11]]
  let v ← o.gW v 2 7 8 13 m'[s[12]] m'[s[13]]
  o.gW v 3 4 9 14 m'[s[14]] m'[s[15]]

end GOps2

namespace GOps2

variable {α S : Type} (o : GOps Blake2sCircuit.m α S)

/-- `initW`. -/
@[specialize] def initW : Vector (Vector α 32) 16 :=
  Vector.ofFn fun w : Fin 16 ↦
    if w.val < 8 then o.inW (32 * w)
    else if w.val < 12 then o.litW constPos iv[w.val - 8]
    else o.xorW (o.litW constPos iv[w.val - 8]) (o.inW (counterLo + 32 * (w.val - 12)))

/-- `compressW`. -/
@[specialize] def compressW : GB S (Vector (Vector α 32) 8) := do
  let msg : Vector (Vector α 32) 16 := Vector.ofFn fun w ↦ o.inW (msgBase + 32 * w)
  let v ← sigma.foldlM (fun v s ↦ o.roundW v msg s) o.initW
  pure (Vector.ofFn fun w : Fin 8 ↦ o.xorW (o.xorW v[w] v[w.val + 8]) (o.inW (32 * w)))

end GOps2

namespace W
def walkAB2 (e wt : Pos Blake2sCircuit.m → F) : F × F :=
  let o := walkOps e wt
  let c := wt constPos
  let r := GOps2.compressW o |>.run ⟨gateBase, (0, 0)⟩
  let s₂ := (outPairs r.1).foldl (fun s p ↦ o.upd s p.1 p.2 c) r.2.acc
  (s₂.1, s₂.2)
def sums (e wt : Pos Blake2sCircuit.m → F) : F × F :=
  let c := wt constPos
  ((∑ k : Pos Blake2sCircuit.m, if k.val < 256 ∨ (512 ≤ k.val ∧ k.val < 1152) then e k * wt k else 0),
   (∑ k : Pos Blake2sCircuit.m, if k.val < 256 ∨ (512 ≤ k.val ∧ k.val < 1152) then e k * c else 0))
def core (e wt : Pos Blake2sCircuit.m → F) : F × F :=
  let o := walkOps e wt
  let r := o.compressW.run ⟨gateBase, (0, 0)⟩
  r.2.acc
end W
end FR

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407
def randF (s : UInt64) : F := let a := lcg (s ^^^ 0x5555); ⟨⟨a⟩, ⟨lcg a⟩⟩
def randAF (seed : UInt64) (n : Nat) : Array F := (Array.range n).map fun i => randF (seed * 7919 + i.toUInt64)
def onPosA (a : Array F) (k : Pos Blake2sCircuit.m) : F := a.getD k.val 0
def ms (t0 t1 : ℕ) : String := s!"{(t1 - t0) / 1000000}.{((t1 - t0) / 10000) % 100} ms"

def main : IO UInt32 := do
  for i in [0:5] do
    let e := randAF (i.toUInt64 + 1) 16384; let w := randAF (i.toUInt64 + 99) 16384
    let a ← IO.monoNanosNow
    let r1 ← IO.lazyPure fun _ => walkAB (onPosA e) (onPosA w)
    let b ← IO.monoNanosNow
    let r2 ← IO.lazyPure fun _ => W.walkAB2 (onPosA e) (onPosA w)
    let c ← IO.monoNanosNow
    let r3 ← IO.lazyPure fun _ => W.sums (onPosA e) (onPosA w)
    let d ← IO.monoNanosNow
    let r4 ← IO.lazyPure fun _ => W.core (onPosA e) (onPosA w)
    let f ← IO.monoNanosNow
    IO.println s!"walkAB {ms a b}  specialised copy (no input sums) {ms b c}  input sums (Finset) {ms c d}  generic core (no sums) {ms d f}  [{r1.1.c₀.val} {r2.1.c₀.val} {r3.1.c₀.val} {r4.1.c₀.val}]"
  return 0
