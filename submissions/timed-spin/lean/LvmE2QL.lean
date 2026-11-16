-- New for lvm2 E2F (slice S1, E2F-QH2): the `KS` link `KSlink` at `E2` (V's `LvmDecideE2.ksLinkD`, the `E2` twin of
-- `LvmQLinkArithKS.ksLinkGadget`/`ksGlueE14`): the challenges, the shift sumcheck from `0`, the four values, the
-- interval shift sums `pre(H)` (`LvmQLinkArithRows.preLevel`'s twelve rows per coordinate, on the `E2` kit), the
-- gated check; and the cells the link's claims need (`eq(λ, ·)`, the selector).
import LvmE2QWKit

/-!
# The `KS` link at `E2` (`ksLinkG2`)

V's `ksLinkD hk xl rows` (`rows = contRowsF = [1, B) ∪ [K + 1, K + 32)`):

* `hk + 5` ground challenges (`ρ = kchal[0, hk)`, `λ = kchal[hk, hk + 5)`), answers `qa + 10 i` (nonce at
  `qa − 1 + 10 i`, PoW lane `qa + 2 + 10 i`);
* the shift sumcheck from `0` (`sc2 hk`, first message `qa + 10 hk + 49`); the four values `Y, in, M, X` after it;
* **the check** `gate·(f + Sc·Y + eqEval(ρ, ρ')·(in + M + sel·X)) = 0`, `Sc = pre(B − 1) + pre(K + 31) + pre(K)`
  (`contShiftF rows ρ ρ'`, `LvmQLinkArith.preCF`), `sel = Π_{j ≥ xl} ρ'_j` (`selXF`).

`KsLinkOut2` also carries `eq(λ, ·)` (32 values) for the link's claims.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build

/-- One coordinate of `preCF` (`LvmQLinkArith.preStep`; `LvmQLinkArithRows.preLevel`'s rows): from the tail's
`(pre, E, Pt)` to this level's, `h` the bound's bit. -/
def g2PreLevel (z : C2) (h : Bool) (x0 y0 : C2) (r : C2 × C2 × C2) : BM (C2 × C2 × C2) :=
  g2One y0 >>= fun l0 => g2One x0 >>= fun l1 =>
  g2Mul l0 x0 z >>= fun l2 => g2Mul y0 l1 z >>= fun l3 => g2Mul l0 l1 z >>= fun l4 => g2Mul y0 x0 z >>= fun l5 =>
  g2Add r.2.1 (if h then r.2.2 else z) >>= fun l6 =>
  g2Mul l3 r.1 z >>= fun l7 => g2Mul l2 l6 l7 >>= fun npre =>
  g2Mul l5 r.2.1 z >>= fun l9 => g2Mul l4 l6 l9 >>= fun nE =>
  g2Mul (if h then l5 else l4) r.2.2 z >>= fun nPt => pure (npre, nE, nPt)

/-- **`preCF xs ys H`**, the last coordinate first (`base = (0, 0, 1)`). -/
def g2PreRec (z : C2) : List C2 → List C2 → Nat → C2 × C2 × C2 → BM (C2 × C2 × C2)
  | x0 :: x, y0 :: y, H, base => g2PreRec z x y (H / 2) base >>= fun r => g2PreLevel z (H % 2 = 1) x0 y0 r
  | _, _, _, base => pure base

/-- `acc · eqEvalF xs ys = acc · Π (1 + x + y)`, one `lin` and one product per coordinate. -/
def g2EqEval (z : C2) : C2 → List C2 → List C2 → BM C2
  | acc, x :: xs, y :: ys => g2Lin 1 1 x y >>= fun f => g2Mul acc f z >>= fun acc' => g2EqEval z acc' xs ys
  | acc, _, _ => pure acc

/-- The `KS` link's outputs. -/
structure KsLinkOut2 where
  /-- The `hk + 5` challenges. -/
  kchal : List C2
  /-- The shift point `ρ'` (`hk`) and the sumcheck's final claim. -/
  shift : List C2
  final : C2
  /-- `Y, in, M, X`. -/
  vals : List C2
  /-- `eq(λ, ·)` (32 values). -/
  om : List C2
  /-- `selXF xl ρ'`. -/
  sel : C2

/-- The lanes of the link from its first answer lane `qa`: the shift sumcheck's first message, the four values. -/
def ksLinkQ1 (hk qa : Nat) : Nat := qa + 10 * hk + 49

/-- The values' lane. -/
def ksLinkQV (hk qa : Nat) : Nat := ksLinkQ1 hk qa + roundLanes2 * hk

/-- **V's `ksLinkD hk xl contRowsF`** at `E2`, `contRowsF = [1, B) ∪ [K + 1, K + 32)` (`B = spongeBlocks`,
`K = ksSplit + 399`), first answer lane `qa`, every check gated by `gate`. -/
def ksLinkG2 (hk xl B K qa : Nat) (gate : Cell) : BM KsLinkOut2 :=
  let kchal := (List.range (hk + 5)).map fun i => ld2 (qa + 10 * i)
  let rho := kchal.take hk
  let vals := (List.range 4).map fun k => ld2 (ksLinkQV hk qa + 2 * k)
  g2Zero (ld2 qa) >>= fun z => g2One z >>= fun one =>
  sc2 hk (ksLinkQ1 hk qa) z >>= fun sh =>
  let rho' := sh.1
  g2PreRec z rho rho' (B - 1) (z, z, one) >>= fun p1 =>
  g2PreRec z rho rho' (K + 31) (z, z, one) >>= fun p2 =>
  g2PreRec z rho rho' K (z, z, one) >>= fun p3 =>
  g2Add p1.1 p2.1 >>= fun s12 => g2Add s12 p3.1 >>= fun cs =>
  g2EqEval z one rho rho' >>= fun ee =>
  g2Prod z one (rho'.drop xl) >>= fun sel =>
  g2Add (vals.getD 1 default) (vals.getD 2 default) >>= fun im =>
  g2Mul sel (vals.getD 3 default) im >>= fun inner =>
  g2Mul ee inner z >>= fun t1 =>
  g2Mul cs (vals.getD 0 default) t1 >>= fun rhs =>
  g2Add sh.2 rhs >>= fun e =>
  g2Assert e gate >>= fun _ =>
  g2EqTab z [one] (kchal.drop hk) >>= fun om =>
  pure ⟨kchal, rho', sh.2, vals, om, sel⟩

/-- The PoW lanes of the link. -/
def ksLinkPow (hk qa : Nat) : List Nat :=
  (List.range (hk + 5)).map (fun i => qa + 10 * i + 2) ++ sc2Pow hk (ksLinkQ1 hk qa)

end Lvm.Q2
