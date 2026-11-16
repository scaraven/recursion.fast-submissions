-- New for lvm2 E2-FT (E2F-QH3): the typed phases' verifier in the node program at stage S2GF (transcript amendment
-- 1: the coordinate-split zerocheck, the wiring over six values, `Φ_Q` on 44 variables), the circuit twin of
-- `LvmTypedVX.dTypedX` (V_S) and `LvmTypedSpecXD.typedProgX` (spec).
import LvmTypedLayQ
import LvmTypedVX

/-!
# The typed phases at S2GF (`typedGX`)

From the typed phases' start `P` (bytes, `pos = ent + msg`, a value at byte `P + 40`), read for read as `dTypedX`:

* `zeroGX`: `τ` (20 samples), `ω`, 20 equality-mode rounds of 2, the six values `A₀ A₁ B₀ B₁ C₀ C₁`, the check
  `final = A₀B₀ + A₁B₁ + C₀ + ω·(A₀B₁ + A₁B₀ + x·A₁B₁ + C₁)`;
* `wireGX`: `γ`, 21 plain rounds from `Σ_{k<6} γ^k v_k`, eight matrix values `v_{o'}` (`o' = o + 4s`) and the four
  region values, the check `final = (v₀ + γv₄ + γ²v₁ + γ³v₅ + γ⁴(v₂ + v₃) + γ⁵(v₆ + v₇))·(Σ rv + virt(r_y))`;
* `relayG`: roll 11's (from `rRPX`);
* `qaccTX`: A23 at `Φ_Q` in 44 variables (`κ` 3, `h` 45, `t`, the zero scalar; `y' = Σ_{o'<8} eq(κ, o')·v_{o'}`);
* `miniG`: roll 11's (from `mbPX`).

The positions differ from roll 11's (`zRP` …) by `ω` (one sample), the three extra values at `r_x`, the four extra
matrix values, `κ`'s third sample and `h`'s 45th scalar.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QTyped

/-- `Φ_Q`'s variables at S2GF (`3 + 20 + 21`). -/
abbrev tVarsX : Nat := 3 + tX + tY

/-! ## Positions from the typed phases' start `P` -/

/-- The zerocheck's rounds (after `τ` and `ω`). -/
def zRPX (P : Nat) : Nat := P + 72 * (tX + 1)
/-- The six values at `r_x` (pending). -/
def zAbcPX (P : Nat) : Nat := zRPX P + 120 * tX
/-- `γ`'s sample. -/
def wGPX (P : Nat) : Nat := zAbcPX P + 144
/-- The wiring's rounds. -/
def wRPX (P : Nat) : Nat := wGPX P + 72
/-- `v_{o'}` (8), then the region values (4) (pending). -/
def wVPX (P : Nat) : Nat := wRPX P + 120 * tY
/-- The relayout's rounds (the 12 values are pending in its first round's entry). -/
def rRPX (P : Nat) : Nat := wVPX P + 288
/-- `v_R` (pending). -/
def rVPX (P : Nat) : Nat := rRPX P + 120 * tR
/-- A23's start (`κ`). -/
def aPX (P : Nat) : Nat := rVPX P + 24
/-- The mini-bus's start: after `κ` (3), `h` (`tVarsX + 1`), `t`, the zero scalar. -/
def mbPX (P : Nat) : Nat := aPX P + 216 + 24 * (tVarsX + 1) + 72 + 24

/-! ## The gadgets -/

/-- **The coordinate-split zerocheck** from `P`. Returns `r_x` and the six values. -/
def zeroGX (z g : Cell) (P : Nat) : BM (List Cell × List Cell) := do
  let tb ← ldEsP ((P + 40) / 8) 9 tX
  let om ← Lvm.QAcc.ldE ((P + 72 * tX + 40) / 8)
  let q ← getPtr
  let fin ← QB.scRunQ3 (binParts tX) (zRPX P / 8) (fun i => tb.1 + i) (fun _ => 1) z
  let v ← ldEs ((zAbcPX P + 40) / 8) 3 6
  let a0 := v.getD 0 z
  let a1 := v.getD 1 z
  let b0 := v.getD 2 z
  let b1 := v.getD 3 z
  let c0 := v.getD 4 z
  let c1 := v.getD 5 z
  -- rel₀ = A₀B₀ + A₁B₁ + C₀
  let t0 ← mulAdd .E a1 b1 c0
  let r0 ← mulAdd .E a0 b0 t0
  -- rel₁ = A₀B₁ + A₁B₀ + x·A₁B₁ + C₁
  let p11 ← mulAdd .E a1 b1 z
  let t1 ← lin .E FK.x 0 c1 p11
  let t2 ← mulAdd .E a1 b0 t1
  let r1 ← mulAdd .E a0 b1 t2
  let t ← mulAdd .E om r1 r0
  assertEq fin t g
  -- the rounds' challenges: the template's cells (`zeroG`'s layout: 3 header cells, 7 per round)
  pure ((List.range tX).map fun i => ec (q.e + 3 + 7 * i), v)

/-- The `PUB` lanes at S2GF: the header's lanes with `acc_in` at `accV + 1` scalars (`750` at `P20F`; roll 11's
`pubLanes` is `747`). V_S's `virtEF` reads `pub.hdrLanes`, whose length follows `acc_in`'s. -/
def pubLanesX (accV : Nat) : Nat := 615 + 3 * (accV + 1)

/-- `virtG` with `n` `PUB` lanes (`pubLanesX`). -/
def virtGX (z o : Cell) (T : TData) (pb n : Nat) (ry : List Cell) : BM Cell := do
  let sP ← regSelG z o ry ⟨T.pub, 10, 0⟩
  let vP ← Lvm.QAcc.qpub (fun i => ry.getD i z) z o 10 11 (pb + 1) n
  let w ← mulAdd .E sP vP z
  let e1 ← eqConstG z o ry T.one
  let w ← add w e1
  match T.qlt with
  | none => pure w
  | some (b, l, cs) => do
    let sQ ← regSelG z o ry ⟨b, l, 0⟩
    let vQ ← dotConstG (fun i => ry.getD i z) z o l cs
    mulAdd .E sQ vQ w

/-- Horner's rule from `acc`: `acc ← γ·acc + x` for `x` in order. -/
def hornerG (γ : Cell) : List Cell → Cell → BM Cell
  | [], acc => pure acc
  | x :: xs, acc => do
    let acc' ← mulAdd .E γ acc x
    hornerG γ xs acc'

/-- `Σ_{k<6} γ^k v_k` by Horner (`v` the six values at `r_x`). -/
def batch6G (z γ : Cell) (v : List Cell) : BM Cell := hornerG γ ((v.take 6).reverse.drop 1) (v.getD 5 z)

/-- **The wiring over the six values** after the zerocheck. Returns `r_y`, the eight matrix values, the four region
values. -/
def wireGX (z o g : Cell) (T : TData) (pb P n : Nat) (v : List Cell) :
    BM (List Cell × List Cell × List Cell) := do
  let γ ← Lvm.QAcc.ldE ((wGPX P + 40) / 8)
  let c0 ← batch6G z γ v
  let q ← getPtr
  let fin ← QB.scRunP3 (binParts tY) (wRPX P / 8) c0
  let ry := (List.range tY).map fun i => ec (q.e + 3 + 6 * i)
  let vs ← ldEs ((wVPX P + 40) / 8) 3 8
  let rv ← ldEs ((wVPX P + 40) / 8 + 24) 3 4
  -- v₀ + γ(v₄ + γ(v₁ + γ(v₅ + γ((v₂ + v₃) + γ(v₆ + v₇)))))
  let d1 ← add (vs.getD 6 z) (vs.getD 7 z)
  let d0 ← add (vs.getD 2 z) (vs.getD 3 z)
  let m4 ← mulAdd .E γ d1 d0
  let m3 ← mulAdd .E γ m4 (vs.getD 5 z)
  let m2 ← mulAdd .E γ m3 (vs.getD 1 z)
  let m1 ← mulAdd .E γ m2 (vs.getD 4 z)
  let m0 ← mulAdd .E γ m1 (vs.getD 0 z)
  let ve ← virtGX z o T pb n ry
  let s ← sumG z (rv ++ [ve])
  let pr ← mulAdd .E m0 s z
  assertEq fin pr g
  pure (ry, vs, rv)

/-- **Q_acc, typed, at 44 variables** from lane `L` (`8 L = aPX P`): `κ'` (3 samples), `h'` (45), `t'`, the zero
scalar; `y' = Σ_{o'<8} eq(κ', o')·v_{o'}`; `h'₀ = acc_in'.y`, `Σ h' = y'`; the line from `acc_in'.pt` to
`κ' ++ r_x ++ r_y` at `t'`, and `h'(t')`, equal to the current proof's `acc_in` (`PUB` lanes `615 + 3j`). -/
def qaccTX (L pb : Nat) (rx ry vs : List Cell) : BM Unit := do
  let g := kc pb
  let zo ← Lvm.QAcc.consts pb
  let kb ← Lvm.QAcc.ldEsB ((List.range 3).map fun i => L + 5 + 9 * i)
  let y ← Lvm.QAcc.qyown kb 1 3 zo.1 zo.2 vs
  let h0 := L + 27
  let hb ← Lvm.QAcc.ldEsB ((List.range (tVarsX + 1)).map fun j => h0 + 5 + 3 * j)
  let ab ← Lvm.QAcc.ldEsB ((List.range (tVarsX + 1)).map Lvm.QAcc.accLane)
  Lvm.QAcc.assertEqE (ec hb) (ec (ab + tVarsX)) g
  let sh ← Lvm.QAcc.macChain ((List.range (tVarsX + 1)).map fun j => (zo.2, ec (hb + j))) zo.1
  Lvm.QAcc.assertEqE sh y g
  let t ← Lvm.QAcc.ldE (h0 + 3 * (tVarsX + 1) + 5)
  let hv ← Lvm.QAcc.horner ((List.range (tVarsX + 1)).map fun j => ec (hb + j)) t zo.1
  let bc := (List.range 3).map (fun j => ec (kb + j)) ++ rx ++ ry
  let pts ← Lvm.QAcc.linePts ((List.range tVarsX).map fun i => (ec (ab + i), bc.getD i (ec 0))) t
  let pc ← Lvm.QAcc.ldEsB ((List.range (tVarsX + 1)).map fun j => pb + 615 + 3 * j)
  let _ ← Lvm.QAcc.assertEqs ((List.range tVarsX).map fun i => (pts.getD i default, ec (pc + i))) g
  Lvm.QAcc.assertEqE hv (ec (pc + tVarsX)) g
  let zz ← Lvm.QAcc.ldE (h0 + 3 * (tVarsX + 1) + 9 + 5)
  assert0 zz g

/-- **The typed backend's verifier at S2GF** from position `P`, the current proof's `PUB` at cell `pb`, `z`/`o` the
`E` constants, `accV` A23's variables (`PUB` has `pubLanesX accV` lanes). `TypedC.abc` holds the six values at `r_x`, `vs` the eight matrix values. -/
def typedGX (T : TData) (pb P accV : Nat) (z o : Cell) : BM TypedC := do
  let g := kc pb
  let zr ← zeroGX z g P
  let w ← wireGX z o g T pb P (pubLanesX accV) zr.2
  let r ← relayG z o g T (rRPX P - rRP 0) w.1 (w.2.2.getD 1 z)
  qaccTX (aPX P / 8) pb zr.1 w.1 w.2.1
  let mb ← miniG z o g T (mbPX P)
  pure ⟨zr.1, w.1, zr.2, w.2.1, w.2.2, r.1, r.2, mb.1, mb.2⟩

/-- **The typed phases' end at S2GF** (after the mini-bus's table phase). -/
def typedEndX (T : TData) (P : Nat) : Nat := tabEnd T.mbS T.mbR (busEndD T.mbD (mbPX P))

end Lvm.E2Q
