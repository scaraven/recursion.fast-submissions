-- New for lvm2 E2F (slice S1, E2F-QH2): the `E2` gadget kit of the front's arithmetic (wire, slots, `KS` link):
-- `C2` values from stream lanes, field gadgets on twin rows, sums, dots, `eq` tables, the `E2` sumcheck round with
-- its nonce lane. Generic in the stream offsets (reused by the S2GT circuit).
import LvmE2QBuild

/-!
# The `E2` gadget kit

Every gadget is a `BM` program on `C2` values (two `K` cells, `LvmE2QGad`), built from the twin rows
`gE2mul`/`gE2lin` (`LvmE2QGad`, `LvmE2QBuild`):

* **stream scalars**: an `E2` scalar of the transcript is two `K` lanes `(re, im)`; at lane `q` it is the value
  `ld2 q = (kc q, kc (q + 1))` (no row); an `E2` challenge at answer lane `q` is `ld2 q` too (lanes 0–1 of the
  answer), its proof-of-work lane is `q + 2`;
* **field gadgets** (the `E3` template kit's names with a `2`): `g2Mul a b d = a·b + d`, `g2Add`, `g2One a = a + 1`,
  `g2Zero a = 0`, `g2Lin`, `mapB`, `g2Sum`, `g2Dot`, `g2EqTab` (`eqKernel`'s table), `g2Prod`;
* **`scRound2 q claim`**: one round of `V`'s `sumcheckD _ claim 3` (`roundPolyD 3 claim none`, then `sampleG`): the
  message `c₀, c₂` at lanes `q … q + 3`, the nonce at `q + 4`, the challenge at `q + 5` (PoW lane `q + 7`); the
  next claim `c₀ + r·(claim + c₂) + r²·c₂`. Rounds are `14` lanes apart (`5` header + `5` message + `4` answer).
* **`sc2 R q claim`**: `R` rounds from lane `q`; `sc2Pow R q`: their PoW lanes.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Values from the stream -/

/-- The `E2` scalar at lanes `q, q + 1`. -/
def ld2 (q : Nat) : C2 := ⟨kc q, kc (q + 1)⟩

/-- A `K` cell as an `E2` value (`im` a `K` zero cell `z`). -/
def kC2 (b z : Cell) : C2 := ⟨b, z⟩

/-! ## Field gadgets -/

/-- `a·b + d`. -/
def g2Mul (a b d : C2) : BM C2 := gE2mul a b d

/-- `a + k·b + k'`. -/
def g2Lin (k : FK) (k' : FE2) (a b : C2) : BM C2 := gE2lin k k' a b

/-- `a + b`. -/
def g2Add (a b : C2) : BM C2 := gE2lin 1 0 a b

/-- `a + 1`. -/
def g2One (a : C2) : BM C2 := gE2lin 0 1 a a

/-- `0` (`a + a`). -/
def g2Zero (a : C2) : BM C2 := gE2lin 1 0 a a

/-- The constant `k` (`a + a + k`). -/
def g2Const (k : FE2) (a : C2) : BM C2 := gE2lin 1 k a a

/-- `f` on every element, in order. -/
def mapB {α β : Type} (f : α → BM β) : List α → BM (List β)
  | [] => pure []
  | a :: as => f a >>= fun b => mapB f as >>= fun bs => pure (b :: bs)

/-- `s + c₀ + c₁ + …`. -/
def g2Sum : C2 → List C2 → BM C2
  | s, [] => pure s
  | s, c :: cs => g2Add s c >>= fun s' => g2Sum s' cs

/-- `acc + Σ a·b`. -/
def g2Dot : C2 → List (C2 × C2) → BM C2
  | acc, [] => pure acc
  | acc, (a, b) :: r => g2Mul a b acc >>= fun acc' => g2Dot acc' r

/-- `acc·x₀·x₁ ⋯` (`z` a zero). -/
def g2Prod (z : C2) : C2 → List C2 → BM C2
  | acc, [] => pure acc
  | acc, x :: xs => g2Mul acc x z >>= fun acc' => g2Prod z acc' xs

/-- One level of an `eq` table (`eqKernelF`'s step): `e·(1 + r)` for every `e`, then `e·r`. -/
def g2EqStep (z : C2) (tab : List C2) (r : C2) : BM (List C2) :=
  g2One r >>= fun r1 => mapB (fun e => g2Mul e r1 z) tab >>= fun lo =>
    mapB (fun e => g2Mul e r z) tab >>= fun hi => pure (lo ++ hi)

/-- **The `eq` table of a point** from `tab` (`[one]` for `eqKernelF`; `z` a zero). -/
def g2EqTab (z : C2) : List C2 → List C2 → BM (List C2)
  | tab, [] => pure tab
  | tab, r :: rs => g2EqStep z tab r >>= fun t => g2EqTab z t rs

/-- `gate·a = 0`, both coordinates (`gate` a `K` cell). -/
def g2Assert (a : C2) (gate : Cell) : BM Unit := assert0 a.re gate >>= fun _ => assert0 a.im gate

/-! ## The `E2` sumcheck -/

/-- The lanes of a sumcheck round (count 3): message `q`, nonce `q + 4`, answer `q + 5`, next round `q + 14`. -/
def roundLanes2 : Nat := 14

/-- **One round** at lane `q` of `V`'s `sumcheckD _ claim 3 [none]`: the challenge and the next claim
`polyEvalF [c₀, claim + c₂, c₂] r`. -/
def scRound2 (q : Nat) (claim : C2) : BM (C2 × C2) :=
  let c0 := ld2 q
  let c2 := ld2 (q + 2)
  let r := ld2 (q + 5)
  g2Add claim c2 >>= fun c1 => g2Mul c2 r c1 >>= fun t => g2Mul t r c0 >>= fun nc => pure (r, nc)

/-- **`R` rounds** from lane `q` (round `k` at `q + 14 k`): the challenges and the final claim. -/
def sc2 : Nat → Nat → C2 → BM (List C2 × C2)
  | 0, _, claim => pure ([], claim)
  | R + 1, q, claim => scRound2 q claim >>= fun rc => sc2 R (q + roundLanes2) rc.2 >>= fun res =>
    pure (rc.1 :: res.1, res.2)

/-- The PoW lanes of `R` rounds from lane `q`. -/
def sc2Pow (R q : Nat) : List Nat := (List.range R).map fun k => q + roundLanes2 * k + 7

/-- The answer lanes (challenges) of `R` rounds from lane `q`. -/
def sc2Ans (R q : Nat) : List Nat := (List.range R).map fun k => q + roundLanes2 * k + 5

end Lvm.Q2
