-- New for lvm2 E2F (slice S1, E2F-QH1): one Keccak GKR layer at `E2` as a loop template (twin rows), the `E2`
-- counterpart of `LvmQKeccakRounds`/`LvmQKeccakLayer`, on S2GF's stream layout (16-B scalars, per-challenge nonces,
-- the separator after `U`).
import LvmE2QKTB

/-!
# One Keccak GKR layer at `E2` (`layerTB2`)

`V`'s `verifyKeccakLayerD` (`LvmDecideE2`) on a table of `2^(P+4)` instances, as `layerTB` (`LvmQKeccakLayer`) with
`E2` values. The carried claim is `C = 57 + P` `E2` values, `2C` `K` copy rows at the template's end (`cb` the
first): `value, μ[16], κ, point[P+1], B[25], a[6], flip[7]`, value `j` in rows `cb + 2j`, `cb + 2j + 1`.

**Stream layout** (lanes from `q`, the layer's first product lane; S2GF, s2gf-items.tsv): the `U` message
`product[47]` at `q + 2k`; the separator's answer at `q + 94`; `s`'s nonce at `q + 103`, its answer at `q + 104`;
the `P + 1` pack rounds from `q + 113`, 14 lanes a round (`c₁, c₂` at `m, m + 2`, the nonce at `m + 4`, the
challenge at `m + 5`); the 11 position rounds from `q + 113 + 14(P+1)`, 16 lanes a round (`c₀, c₂, c₃` at
`m, m + 2, m + 4`, the nonce at `m + 6`, the challenge at `m + 7`); `t[3]` at `q₃ = q + 289 + 14(P+1)`, `β`'s nonce
at `q₃ + 6`, its answer at `q₃ + 7`. A layer is `305 + 14(P+1)` lanes (`LCfg.str2`). Every `E2` challenge is the
answer's lanes 0–1; its nonce is the lane before the answer (the PoW range rows on lane 2 are not this module's).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-- Lanes per layer at `E2`. -/
def LCfg.str2 (c : LCfg) : Nat := 421 + 14 * (c.P + 1)

/-- A carried `E2` input (the previous iteration's copy `j`). -/
def LCfg.pv2 (c : LCfg) (j : Nat) : S2 := (.prev (c.cb + 2 * j), .prev (c.cb + 2 * j + 1))

/-! ## Pack rounds and position rounds -/

/-- One pack round at `E2`: message `c₁, c₂` at lanes `q, q + 2`, the challenge at `q + 5`. Returns the new value,
the new scale and the challenge. -/
def q2PackRound (z : S2) (q : Nat) (str : List Nat) (r value scale : S2) : TB (S2 × S2 × S2) :=
  let c1 := lane2 q str
  let c2 := lane2 (q + 2) str
  let ch := lane2 (q + 5) str
  q2Add c1 c2 >>= fun s => q2Mul r s value >>= fun c0 => q2Mul c2 ch c1 >>= fun h =>
  q2Mul h ch c0 >>= fun pe => q2Lin 1 1 r ch >>= fun g => q2Mul g pe z >>= fun v' =>
  q2Mul scale g z >>= fun s' => pure (v', s', ch)

/-- The pack rounds from lane `q` (14 lanes a round). -/
def q2PackRounds (z : S2) (str : List Nat) : Nat → List S2 → S2 → S2 → TB (S2 × S2 × List S2)
  | _, [], value, scale => pure (value, scale, [])
  | q, r :: rs, value, scale =>
    q2PackRound z q str r value scale >>= fun a =>
      q2PackRounds z str (q + 14) rs a.1 a.2.1 >>= fun b => pure (b.1, b.2.1, a.2.2 :: b.2.2)

/-- One position round at `E2`: `c₀, c₂, c₃` at lanes `q, q + 2, q + 4`, the challenge at `q + 7`. -/
def q2LocalRound (q : Nat) (str : List Nat) (value : S2) : TB (S2 × S2) :=
  let c0 := lane2 q str
  let c2 := lane2 (q + 2) str
  let c3 := lane2 (q + 4) str
  let ch := lane2 (q + 7) str
  q2Add value c2 >>= fun s => q2Add s c3 >>= fun c1 =>
  q2Mul c3 ch c2 >>= fun h1 => q2Mul h1 ch c1 >>= fun h2 => q2Mul h2 ch c0 >>= fun h3 => pure (h3, ch)

/-- The position rounds from lane `q` (16 lanes a round). -/
def q2LocalRounds (str : List Nat) : Nat → Nat → S2 → TB (S2 × List S2)
  | 0, _, value => pure (value, [])
  | k + 1, q, value =>
    q2LocalRound q str value >>= fun a => q2LocalRounds str k (q + 16) a.1 >>= fun b => pure (b.1, a.2 :: b.2)

/-! ## The layer -/

/-- **The layer at `E2`.** -/
def layerTB2 (c : LCfg) : TB Unit :=
  let str := [c.str2]
  let value := c.pv2 0
  let mu := (List.range 32).map fun i => c.pv2 (1 + i)
  let kappa := c.pv2 33
  let point := (List.range (c.P + 1)).map fun i => c.pv2 (34 + i)
  let B := (List.range 25).map fun l => c.pv2 (35 + c.P + l)
  let a := (List.range 6).map fun i => c.pv2 (60 + c.P + i)
  let flips := (List.range 7).map fun i => c.pv2 (66 + c.P + i)
  let q := c.q
  let prod := (List.range productBits).map fun k => lane2 (q + 2 * k) str
  let s := lane2 (q + 220) str
  q2Base (.ext ⟨.K, q, str⟩) >>= fun base =>
  let zK := base.1
  let z := base.2.1
  let one := base.2.2
  q2Proj4 z rmfeProject mu prod >>= fun proj =>
  q2One (point.getD c.P default) >>= fun seg0 =>
  q2Dot z ((List.range 7).map fun i => (kS2 (c.k i) zK, flips.getD i default)) >>= fun in0 =>
  q2Dot z ((List.range 7).map fun i => (kS2 (c.k (7 + i)) zK, flips.getD i default)) >>= fun in1 =>
  q2Dot z [(seg0, in0), (point.getD c.P default, in1)] >>= fun iota =>
  q2Mul iota kappa proj >>= fun e1 => q2Add e1 value >>= fun e1' => q2Assert e1' (c.k 15) >>= fun _ =>
  q2Inst4 z one s rmfeEmbed >>= fun mk =>
  q2Horner s (prod.getD 104 default) ((List.range 104).reverse.map fun k => prod.getD k default) >>= fun v0 =>
  q2PackRounds z str (q + 229) point v0 one >>= fun pk =>
  q2LocalRounds str 11 (q + 229 + 14 * (c.P + 1)) pk.1 >>= fun lc =>
  let q3 := q + 405 + 14 * (c.P + 1)
  let t := (List.range 3).map fun k => lane2 (q3 + 2 * k) str
  let beta := lane2 (q3 + 7) str
  q2EqTab z [one] (lc.2.take 3) >>= fun tbLo => q2EqTab z [one] ((lc.2.drop 3).take 3) >>= fun tbHi =>
  q2EqTab z [one] (a.take 3) >>= fun taLo => q2EqTab z [one] (a.drop 3) >>= fun taHi =>
  q2EqTab z [one] (lc.2.drop 6) >>= fun eL =>
  mapT2 (q2LowTab z taLo tbLo 0) (List.range 8) >>= fun L0 =>
  mapT2 (q2LowTab z taLo tbLo 1) (List.range 8) >>= fun L1 =>
  mapT2 (q2HighTab z taHi tbHi) (List.range 8) >>= fun H =>
  mapT2 (q2Shift z L0 L1 H) (List.range 64) >>= fun sh =>
  q2SumMap z 25 (fun l => q2LaneForm z B (fun r => sh.getD r default) l >>= fun lf =>
    q2Mul (eL.getD l default) lf z) >>= fun Wk =>
  q2SumMap z 25 (fun l => q2Mul (eL.getD l default) (B.getD l default) z) >>= fun dfB =>
  q2Index z 0 one (lc.2.take 6) >>= fun idx => q2Mul dfB idx z >>= fun Wf =>
  q2Add Wf Wk >>= fun d => q2Mul (kS2 (c.k 14) zK) d Wk >>= fun W =>
  q2Mul mk.2 (t.getD 0 default) z >>= fun kt0 => q2Add mk.2 (t.getD 1 default) >>= fun k1 =>
  q2Mul k1 (t.getD 2 default) kt0 >>= fun m => q2Mul pk.2.1 W z >>= fun sw => q2Mul sw m lc.1 >>= fun e2 =>
  q2Assert e2 (c.k 15) >>= fun _ =>
  q2Mul beta (t.getD 2 default) (t.getD 1 default) >>= fun tt => q2Mul beta tt (t.getD 0 default) >>= fun v' =>
  q2LaneW eL beta >>= fun B' =>
  q2EqTab z [one] (lc.2.take 6) >>= fun A' =>
  mapT2 (q2Flip z B' A') (List.range 7) >>= fun fl =>
  mapT2 q2Copy ([v'] ++ mk.1 ++ [mk.2] ++ pk.2.2 ++ B' ++ lc.2.take 6 ++ fl) >>= fun _ => pure ()

/-- The first carried copy row of the `E2` layer template. -/
def cbOf2 (P : Nat) : Nat := (layerTB2 ⟨P, 0, 0, 0⟩ 0).2.length - 2 * (73 + P)

/-- The `E2` layer at the origin. -/
def lay02 (P : Nat) : LCfg := ⟨P, 0, 0, cbOf2 P⟩

/-- The `E2` layer template at the origin. -/
def layIns2 (P : Nat) : List Ins := (layerTB2 (lay02 P) 0).2

/-- The `E2` layer template, its lanes from `q`, its constants from `cst`. -/
def layTpl2 (P q cst : Nat) : List LRow := tplOf ((layIns2 P).map (relocI q cst))

/-- The structural facts of the `E2` layer template (decided per `P`): its length is `cb + 2C`, every assertion is
gated by constant `15`, the last `2C` rows are `e2` copy rows. -/
def layOk2 (P : Nat) : Bool :=
  (layIns2 P).length == cbOf2 P + 2 * (73 + P) &&
  (layIns2 P).all (fun i => i.op != .assert0 || i.args.getD 1 default == (lay02 P).k 15) &&
  ((layIns2 P).drop (cbOf2 P)).all fun i => i.ty == .K && i.op != .assert0

end Lvm.Q1
