-- New for lvm2 E2F (slice S1, E2F-QH2): the chain wiring phase `CHwire` at `E2` (V's `LvmDecideE2.wireD`, the
-- `E2` twin of `LvmQWire.wireGadget`). The gadgets are `LvmQWire`'s, transcribed onto the `E2` kit (`LvmE2QWKit`):
-- the same rows' algebra (`thrEvalF`, `msEvalF`, `wireTargetF`, `slotWF` over a field), `C2` operands.
import LvmE2QWKit
import LvmQKeccakSpec
import LvmDecideKeccak

/-!
# The wiring gadget at `E2` (`wireG2`)

V's `wireD w sb dsel s n claim` (`LvmDecideE2`) on the tape's input claim (`cv`, H1's tape output in
`LvmQWire`'s layout: `value, μ[32], κ, point[P+1], B[25], a[6], …`, every entry a `C2`):

1. **`preW2`**: the `eq` table of `a`; `ω_j` at `wPos` as `laneForm B (eq(a, · + z))`; `ι(0)`; `thrEvalF ρ μ (m)`;
   `padDot`; the target `value + ι(0)·padDot + c43Dot·(thr + ι(0))` (`wireTargetF`).
2. **The wiring sumcheck** (`sc2 w`, `w = P + 6` rounds from lane `qw`).
3. **`postW2`**: `g_D` (lane `qw + 14 w`), the gated check `gate·(final + msEvalF ρ μ σ (m) · g_D) = 0`.
4. **`D`'s slot sumcheck** (`sc2 2` from lane `qw + 14 w + 2`, starting at `g_D`) and **`slotW2`**: the 64 slices
   (lanes `qw + 14 w + 30 + 2 z`), the weights `W_z(τ) = Σ_{o<4} eq(τ, o)·ω_{8+64o+z}`, the gated check
   `gate·(final' + Σ_z W_z·slice_z) = 0`.

The row switch of the slices (`rowSwitchD`, seven `E3` answers from lane `qw + 14 w + 158`, 9 apart) is
`LvmQRingRow.rowG`; `wireOut2` gives its point `σ ‖ τ ‖ selPt(dsel)` and slice lanes.

The bits of `m = n − 1` (`mb`) and of `s'` (`sb`) are `K` cells (`kC2` with the `K` zero `zk`).
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## `ω` -/

/-- `0, 1, 6`, `8 … 264`, `1087` (`LvmQWire.wPos`). -/
def wPos : List Nat := [0, 1, 6] ++ (List.range 257).map (· + 8) ++ [1087]

/-- The index of `ω_{8+p}` in `wPos`. -/
def wIx (p : Nat) : Nat := 3 + p

/-- `laneForm B R ℓ` (`LvmQKeccakParts2.gLaneForm`). -/
def g2LaneForm (z : C2) (B : List C2) (R : Nat → C2) (l : Nat) : BM C2 :=
  g2Mul (B.getD (keccakPi l) default) (R (Lvm.Q1.rho l)) z >>= fun t1 =>
  g2Dot t1 ((List.range 5).map fun y =>
    (B.getD (keccakPi ((l % 5 + 1) % 5 + 5 * y)) default, R (Lvm.Q1.rho ((l % 5 + 1) % 5 + 5 * y)))) >>= fun t2 =>
  g2Dot t2 ((List.range 5).map fun y =>
    (B.getD (keccakPi ((l % 5 + 4) % 5 + 5 * y)) default, R ((Lvm.Q1.rho ((l % 5 + 4) % 5 + 5 * y) + 1) % 64)))

/-- `ω_j = laneForm B (s ↦ eq(a, (j mod 64 + s) mod 64)) (j / 64)`. -/
def g2Omega (z : C2) (B eZ : List C2) (j : Nat) : BM C2 :=
  g2LaneForm z B (fun s => eZ.getD ((j % 64 + s) % 64) default) (j / 64)

/-! ## `thrEvalF` -/

/-- One bit of `thrTail` (`LvmQWire.gThrStep`). -/
def g2ThrStep (z r b : C2) (q : C2 × C2) : BM (C2 × C2) :=
  g2Add q.1 q.2 >>= fun d => g2Mul b r z >>= fun t => g2Add r t >>= fun u => g2Mul u d q.1 >>= fun n1 =>
  g2Add b t >>= fun w => g2Mul w d q.2 >>= fun n2 => pure (n1, n2)

/-- `thrTail ρ tb` from the top bit down. -/
def g2ThrTail (z one : C2) : List C2 → List C2 → BM (C2 × C2)
  | r :: ρ, b :: tb => g2ThrTail z one ρ tb >>= fun q => g2ThrStep z r b q
  | _, _ => pure (one, z)

/-- The prefix sums of the `eq` table of `tb4` (`lt e = Σ_{j<e} eq(tb4, j)`). -/
def g2LtTab (z one : C2) (tb4 : List C2) : BM (List C2) :=
  g2EqTab z [one] tb4 >>= fun e =>
  mapB (fun k => g2Sum z (e.take k)) (List.range 33)

/-- **`thrEvalF ρ μ tb`**. -/
def g2Thr (z one : C2) (ρ μ tb lt : List C2) : BM C2 :=
  g2ThrTail z one ρ (tb.drop 5) >>= fun q =>
  g2Sum z μ >>= fun sm =>
  g2Dot z ((List.range 32).map fun d => (μ.getD d default, lt.getD d default)) >>= fun L =>
  g2Add q.1 q.2 >>= fun d => g2Mul sm q.1 z >>= fun x => g2Mul d L x

/-! ## `msEvalF` -/

/-- The four entries `(c, s) = 00, 01, 10, 11`. -/
abbrev Q4 := C2 × C2 × C2 × C2

/-- `msStep` for a known bit `t`. -/
def g2MsStep (z : C2) (al be ga de : C2) (t : Bool) (q : Q4) : BM Q4 :=
  let (q00, q01, q10, q11) := q
  if t then
    g2Dot z [(al, q00), (be, q00)] >>= fun f00 => g2Dot z [(al, q00), (be, q01)] >>= fun f01 =>
    g2Dot z [(ga, q00), (de, q10)] >>= fun f10 => g2Dot z [(ga, q01), (de, q10)] >>= fun f11 =>
    pure (f00, f01, f10, f11)
  else
    g2Dot z [(al, q00), (be, q01)] >>= fun f00 => g2Dot z [(al, q01), (be, q01)] >>= fun f01 =>
    g2Dot z [(ga, q01), (de, q10)] >>= fun f10 => g2Dot z [(ga, q01), (de, q11)] >>= fun f11 =>
    pure (f00, f01, f10, f11)

/-- `f₀ + b·(f₁ + f₀)`. -/
def g2Mix (b f1 f0 : C2) : BM C2 := g2Add f1 f0 >>= fun d => g2Mul b d f0

/-- `msStep a r b q` for a bit cell `b`. -/
def g2MsStepA (z a r b : C2) (q : Q4) : BM Q4 :=
  g2Mul a r z >>= fun ar => g2Add a r >>= fun s => g2Add s ar >>= fun al0 => g2One al0 >>= fun al =>
  g2Add r ar >>= fun ga => g2Add a ar >>= fun de =>
  g2MsStep z al ar ga de true q >>= fun f1 => g2MsStep z al ar ga de false q >>= fun f0 =>
  g2Mix b f1.1 f0.1 >>= fun n00 => g2Mix b f1.2.1 f0.2.1 >>= fun n01 =>
  g2Mix b f1.2.2.1 f0.2.2.1 >>= fun n10 => g2Mix b f1.2.2.2 f0.2.2.2 >>= fun n11 =>
  pure (n00, n01, n10, n11)

/-- `msTail σ ρ tb` from the top bit down. -/
def g2MsTail (z one : C2) : List C2 → List C2 → List C2 → BM Q4
  | a :: σ, r :: ρ, b :: tb => g2MsTail z one σ ρ tb >>= fun q => g2MsStepA z a r b q
  | _, _, _ => pure (one, z, z, z)

/-- **`msEvalF ρ μ σ tb 1`** (`|σ| = |tb| = |ρ| + 4`). -/
def g2Ms (z one : C2) (ρ μ σ tb lt : List C2) : BM C2 :=
  g2MsTail z one (σ.drop 5) (ρ.take (σ.length - 5)) (tb.drop 5) >>= fun q =>
  g2EqTab z [one] (σ.take 5) >>= fun e4 =>
  mapB (fun d => g2Mul (e4.getD d default) (μ.getD ((d + 1) % 32) default) z) (List.range 32) >>= fun A =>
  g2Sum z (A.take 31) >>= fun sA =>
  g2Dot z ((List.range 31).map fun d => (A.getD d default, lt.getD (d + 1) default)) >>= fun L =>
  g2Mul sA q.1 z >>= fun x1 => g2Mul (A.getD 31 default) q.2.2.1 x1 >>= fun x2 =>
  g2Add q.2.1 q.1 >>= fun d => g2Mul d L x2

/-- `eq(ρ, 0) = Π_k (1 + ρ_k)`, from `acc`. -/
def g2Eq0 (z : C2) : C2 → List C2 → BM C2
  | acc, [] => pure acc
  | acc, r :: rs => g2One r >>= fun r1 => g2Mul acc r1 z >>= fun acc' => g2Eq0 z acc' rs

/-! ## The blocks -/

/-- What `preW2` exports. -/
structure PreW2 where
  /-- Zero and one. -/
  z : C2
  one : C2
  /-- `ω` at `wPos`. -/
  om : List C2
  /-- The `lt` table of `m`'s low five bits. -/
  lt : List C2
  /-- The wiring sumcheck's claim. -/
  target : C2

/-- **The target block** (`cv` the input claim, `mb` `m`'s bits, `sb` `s'`'s 256 bits, `P + 1 = |ρ|`). -/
def preW2 (P : Nat) (cv : Nat → C2) (mb sb : List C2) : BM PreW2 :=
  let value := cv 0
  let mu := (List.range 32).map fun i => cv (1 + i)
  let rho := (List.range (P + 1)).map fun i => cv (34 + i)
  let B := (List.range 25).map fun l => cv (35 + P + l)
  let a := (List.range 6).map fun i => cv (60 + P + i)
  g2Zero value >>= fun z => g2One z >>= fun one =>
  g2EqTab z [one] a >>= fun eZ =>
  mapB (g2Omega z B eZ) wPos >>= fun om =>
  g2Eq0 z one rho >>= fun e0 =>
  g2Mul e0 (mu.getD 0 default) z >>= fun io0 =>
  g2LtTab z one (mb.take 5) >>= fun lt =>
  g2Thr z one rho mu mb lt >>= fun thr =>
  g2Sum z [om.getD 0 default, om.getD 1 default, om.getD 2 default, om.getD 259 default,
    om.getD 260 default] >>= fun c43 =>
  g2Dot c43 ((List.range 256).map fun p => (om.getD (wIx p) default, sb.getD p default)) >>= fun pd =>
  g2Add thr io0 >>= fun ti => g2Mul c43 ti value >>= fun t1 => g2Mul io0 pd t1 >>= fun tgt =>
  pure ⟨z, one, om, lt, tgt⟩

/-- **The final check** `gate·(final + msEvalF ρ μ σ (m) · g_D) = 0`, `g_D` at lane `qg`. -/
def postW2 (P qg : Nat) (cv : Nat → C2) (mb σ lt : List C2) (z one final : C2) (gate : Cell) : BM C2 :=
  let mu := (List.range 32).map fun i => cv (1 + i)
  let rho := (List.range (P + 1)).map fun i => cv (34 + i)
  let g := ld2 qg
  g2Ms z one rho mu σ mb lt >>= fun ms =>
  g2Mul ms g final >>= fun e => g2Assert e gate >>= fun _ => pure g

/-- The 64 slices at lanes `qs + 2 z`. -/
def slices2 (qs : Nat) : List C2 := (List.range 64).map fun k => ld2 (qs + 2 * k)

/-- **The slot check** `gate·(final' + Σ_z W_z(τ)·slice_z) = 0`, the slices at lanes `qs + 2 z`. -/
def slotW2 (qs : Nat) (om τ : List C2) (z one final : C2) (gate : Cell) : BM Unit :=
  let sl := slices2 qs
  g2EqTab z [one] τ >>= fun et =>
  mapB (fun zz => g2Dot z ((List.range 4).map fun o => (et.getD o default, om.getD (wIx (64 * o + zz)) default)))
    (List.range 64) >>= fun W =>
  g2Dot final ((List.range 64).map fun zz => (W.getD zz default, sl.getD zz default)) >>= fun e =>
  g2Assert e gate

/-! ## The phase -/

/-- The lanes of the phase from its first message lane `qw` (`w` wiring rounds). -/
structure WireLanes where
  /-- `g_D`. -/
  gD : Nat
  /-- The slot sumcheck's first message. -/
  slot : Nat
  /-- The 64 slices. -/
  slices : Nat
  /-- The row switch's first `E3` answer (then every 9 lanes). -/
  ring : Nat
  /-- The phase's end: the next phase's first message (no message pending). -/
  next : Nat

/-- **The lanes of `CHwire`** (STATUS-P (5), s2gf-items: `w` rounds, `g_D` joined to the slot's first message,
two slot rounds, the slices as the first ring sample's message, seven samples). -/
def wireLanes (w qw : Nat) : WireLanes :=
  let gD := qw + roundLanes2 * w
  let slot := gD + 2
  let slices := slot + 2 * roundLanes2
  let ring := slices + 128
  ⟨gD, slot, slices, ring, ring + 9 * 6 + 4 + 5⟩

/-- The gadget's outputs. -/
structure WireOut2 where
  /-- The wiring point `σ` (`w` values). -/
  sigma : List C2
  /-- The final claim of the wiring sumcheck. -/
  final : C2
  /-- `g_D`. -/
  gD : C2
  /-- The slot point `τ` (2 values). -/
  tau : List C2
  /-- The slices. -/
  slices : List C2
  /-- Zero and one. -/
  z : C2
  one : C2

/-- **V's `wireD`** without the row switch (`w = P + 5` rounds from lane `qw`; `cv` the tape's claim, `mb` `m`'s bits,
`sb` `s'`'s bits, both `K` cells, `zk` a `K` zero, `gate` the node flag). -/
def wireG2 (P qw : Nat) (cv : Nat → C2) (mb sb : List Cell) (zk gate : Cell) : BM WireOut2 :=
  let w := P + 6
  let L := wireLanes w qw
  let mb2 := mb.map fun b => kC2 b zk
  let sb2 := sb.map fun b => kC2 b zk
  preW2 P cv mb2 sb2 >>= fun G =>
  sc2 w qw G.target >>= fun sc =>
  postW2 P L.gD cv mb2 sc.1 G.lt G.z G.one sc.2 gate >>= fun g =>
  sc2 2 L.slot g >>= fun sl =>
  slotW2 L.slices G.om sl.1 G.z G.one sl.2 gate >>= fun _ =>
  pure ⟨sc.1, sc.2, g, sl.1, slices2 L.slices, G.z, G.one⟩

/-- The PoW lanes of the phase (`w` wiring rounds, then two slot rounds). -/
def wirePow (w qw : Nat) : List Nat := sc2Pow w qw ++ sc2Pow 2 (wireLanes w qw).slot

end Lvm.Q2
