-- New for lvm2 U-TAPE (UT-C): the wire gadget of stage S2GU at `E2` (`CHwire`: BLUEPRINT2 §1.2 T3–T4 with `KS13`'s
-- sponge rows in the tape's upper half). Built on QH2's `E2` wire kit (`LvmE2QW`): the target, the `MS` automaton of
-- `K̃_ch`, the slot check of `D`; new here: the constant-bound `MS` automaton (`K̃_ks`), `Ĩ_ks`, and the slot weights
-- of the `Y` and `M` blocks as a cyclic convolution of `ω`'s lane forms.
import LvmE2QW
import LvmE2VProg
import LvmVFastQ
import LvmE2QKGkr

/-!
# The wire gadget at S2GU (`wireGU`)

The tape's input claim (`cv`, `LvmE2QKGkr`'s carried values: `value, μ[16], κ, ρ[17], B[25], a[6], …`; `P = 16`, so
`ρ ∈ E2^17`) is reduced by one sumcheck over `x < 2^20` of

`T(x) = K_ch(x)·G_D(x) + K_ks(x)·G_Y(x) + I_ks(x)·G_M(x)`,

then three slot reductions (`D`: 2 rounds, `Y`: 5, `M`: 5), each with its 64 slices and its row switch.

* **`preWU`**: QH2's `preW2` with `thrEval ρ μ m = (1 + ρ₁₆)·thrEval ρ_{<16} μ m` (`thrEval_append`: `m < 2^20`).
* **`kchU`**: `K̃_ch(σ) = msEval ρ μ σ 0 m = (1 + ρ₁₆)·msEvalA ρ_{<16} μ σ (m)` (QH2's `g2Ms`).
* **`kksU`**: `K̃_ks(σ') = Σ_{[a, b] ∈ cont} (MS_13^{2^20}(σ'; b) − MS_13^{2^20}(σ'; a − 1))` for the two intervals
  `[1, B − 1]` and `[K + 1, K + 31]` (`MS(·; 0) = 0`): the automaton `msTail` on the constant bits of `b`, the low digit
  by `t mod 16`, the top factor `cTop = eq(ρ_{9…16}, 2^7) = Π_{k=9}^{15}(1 + ρ_k)·ρ₁₆`.
* **`ikU`**: `Ĩ_ks(σ') = (Σ_d eq(σ'_{<4}, d)·μ_d)·Π_{i<9}(1 + ρ_i + σ'_{4+i})·cTop` (`ikEval`).
* The final check `gate·(final + K̃_ch·g_D + e'·(K̃_ks·g_Y + Ĩ_ks·g_M)) = 0`, `e' = Π_{k=13}^{19}(1 + σ_k)`.
* **`slotWU qs nl om τ`** (`Y`: 25 lanes, `M`: 17): `W_z(τ) = Σ_{l<nl} eq(τ, l)·ω(64 l + z)`. With
  `ω(64 l + z) = laneForm B (s ↦ eZ[(z + s) mod 64]) l` (`eZ = eq(a, ·)`), the three groups of `laneForm`'s terms
  give `W_z = Σ_o C_o·eZ[(z + o) mod 64]` with `C_{ρ_m} ∋ B[π m]·(eq(τ, m)·[m < nl] + E_{(m+4) mod 5})` and
  `C_{ρ_m + 1} ∋ B[π m]·E_{(m+1) mod 5}`, `E_x = Σ_{l<nl, l ≡ x} eq(τ, l)` (`m mod 5` for `m`'s column).
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## The target -/

/-- What `preWU` exports. -/
structure PreWU where
  /-- Zero and one. -/
  z : C2
  one : C2
  /-- `ω` at `wPos` (the target's and `D`'s slot weights). -/
  om : List C2
  /-- The `eq` table of `a` (64 values). -/
  eZ : List C2
  /-- The `lt` table of `m`'s low four bits. -/
  lt : List C2
  /-- The wiring sumcheck's claim. -/
  target : C2

/-- **The target block at S2GU** (`P + 1 = |ρ| = 17`): `preW2`'s rows with the threshold sum scaled by `1 + ρ_P`. -/
def preWU (P : Nat) (cv : Nat → C2) (mb sb : List C2) : BM PreWU :=
  let value := cv 0
  let mu := (List.range 16).map fun i => cv (1 + i)
  let rho := (List.range (P + 1)).map fun i => cv (18 + i)
  let B := (List.range 25).map fun l => cv (19 + P + l)
  let a := (List.range 6).map fun i => cv (44 + P + i)
  g2Zero value >>= fun z => g2One z >>= fun one =>
  g2EqTab z [one] a >>= fun eZ =>
  mapB (g2Omega z B eZ) wPos >>= fun om =>
  g2Eq0 z one rho >>= fun e0 =>
  g2Mul e0 (mu.getD 0 default) z >>= fun io0 =>
  g2LtTab z one (mb.take 4) >>= fun lt =>
  g2Thr z one rho mu mb lt >>= fun thr0 =>
  g2One (rho.getD P default) >>= fun r1 =>
  g2Mul thr0 r1 z >>= fun thr =>
  g2Sum z [om.getD 0 default, om.getD 1 default, om.getD 2 default, om.getD 259 default,
    om.getD 260 default] >>= fun c43 =>
  g2Dot c43 ((List.range 256).map fun p => (om.getD (wIx p) default, sb.getD p default)) >>= fun pd =>
  g2Add thr io0 >>= fun ti => g2Mul c43 ti value >>= fun t1 => g2Mul io0 pd t1 >>= fun tgt =>
  pure ⟨z, one, om, eZ, lt, tgt⟩

/-! ## The kernels -/

/-- The automaton's coefficients of one bit `(σ_k, ρ_k)`: `(1 + a)(1 + r)`, `a r`, `r (1 + a)`, `a (1 + r)`. -/
def msCoef (z a r : C2) : BM (C2 × C2 × C2 × C2) :=
  g2Mul a r z >>= fun ar => g2Add a r >>= fun s => g2Add s ar >>= fun al0 => g2One al0 >>= fun al =>
  g2Add r ar >>= fun ga => g2Add a ar >>= fun de => pure (al, ar, ga, de)

/-- **`msTail` on a constant bound** (bits `t, t / 2, …` low first, one per coefficient quadruple; the top state
`(1, 0, 0, 0)`: `t` has no bit above the coefficients). -/
def msTailC (z one : C2) : List (C2 × C2 × C2 × C2) → Nat → BM Q4
  | [], _ => pure (one, z, z, z)
  | c :: cs, t => msTailC z one cs (t / 2) >>= fun q => g2MsStep z c.1 c.2.1 c.2.2.1 c.2.2.2 (t % 2 == 1) q

/-- **`MS(σ'; t)` without its top factor** for a constant `t`: the low digit's sums (`A_d = eq(σ'_{<4}, d)·μ_{d+1}`,
`d < 15`, split at `t mod 16`) against the automaton's states, `+ A₁₅·q₁₀`. -/
def msConstU (z one : C2) (cs : List (C2 × C2 × C2 × C2)) (A : List C2) (t : Nat) : BM C2 :=
  msTailC z one cs (t / 16) >>= fun q =>
  g2Sum z ((List.range (t % 16)).map fun d => A.getD d default) >>= fun lo =>
  g2Sum z (((List.range 15).drop (t % 16)).map fun d => A.getD d default) >>= fun hi =>
  g2Dot z [(q.1, lo), (q.2.1, hi), (q.2.2.1, A.getD 15 default)]

/-- What the kernels give the final check. -/
structure KernU where
  /-- `K̃_ch(σ)`. -/
  kch : C2
  /-- `K̃_ks(σ')`. -/
  kks : C2
  /-- `Ĩ_ks(σ')`. -/
  iks : C2
  /-- `e' = Π_{k=13}^{19}(1 + σ_k)`. -/
  e' : C2

/-- **The kernels at the wire point** `σ` (20 values; `σ' = σ_{<13}`; `ρ` 17 values, `μ` 16; `mb` `m`'s 20 bits;
the sponge's `cont` intervals `[1, B − 1]`, `[K + 1, K + 31]`). -/
def kernU (z one : C2) (rho mu σ mb lt : List C2) (B K : Nat) : BM KernU :=
  -- `K̃_ch`
  g2Ms z one rho mu σ mb lt >>= fun ms =>
  g2One (rho.getD 16 default) >>= fun r16 =>
  g2Mul ms r16 z >>= fun kch =>
  -- the top factor of the sponge half at `w = 13`: `eq(ρ_{9…16}, 2^7)`
  g2Eq0 z (rho.getD 16 default) ((rho.drop 9).take 7) >>= fun cTop =>
  -- the low digit of `σ'`
  g2EqTab z [one] (σ.take 4) >>= fun e4 =>
  mapB (fun d => g2Mul (e4.getD d default) (mu.getD ((d + 1) % 16) default) z) (List.range 16) >>= fun A =>
  -- `K̃_ks`: the automaton's coefficients on `σ'_{4…12}`, `ρ_{0…8}`; three bounds (`MS(·; 0) = 0`)
  mapB (fun k => msCoef z (σ.getD (4 + k) default) (rho.getD k default)) (List.range 9) >>= fun cs =>
  msConstU z one cs A (B - 1) >>= fun m1 =>
  msConstU z one cs A (K + 31) >>= fun m2 =>
  msConstU z one cs A K >>= fun m3 =>
  g2Sum m1 [m2, m3] >>= fun ms3 =>
  g2Mul ms3 cTop z >>= fun kks =>
  -- `Ĩ_ks`
  g2Dot z ((List.range 16).map fun d => (e4.getD d default, mu.getD d default)) >>= fun dg =>
  mapB (fun k => g2Add (rho.getD k default) (σ.getD (4 + k) default) >>= g2One) (List.range 9) >>= fun fs =>
  g2Prod z dg fs >>= fun ik0 =>
  g2Mul ik0 cTop z >>= fun iks =>
  -- `e'`
  g2Eq0 z one ((σ.drop 13).take 7) >>= fun e' =>
  pure ⟨kch, kks, iks, e'⟩

/-! ## The slot weights of `Y` and `M` -/

/-- The offsets of `laneForm`'s terms: lane `m`'s value enters at `ρ_m` and at `ρ_m + 1` (mod 64). -/
def convOffs : List Nat :=
  ((List.range 25).map Lvm.Q1.rho ++ (List.range 25).map fun m => (Lvm.Q1.rho m + 1) % 64).eraseDups

/-- `C` cells as a template's fixed operand. -/
def c2Ext (c : C2) : Lvm.Q1.S2 := (.ext c.re.addr, .ext c.im.addr)

/-- **The convolution's loop template** (iteration `z < 64`): `W_z = Σ_i C_i·eZ2[z + o_i]`, a chain of twin products
from the zero `z0`, `eZ2` the 128 twin pairs from the `K` cell `b` (`eZ2[t]` at `b + 2t`). -/
def convIns (z0 : C2) (C : List C2) (b : Nat) : List Lvm.Q1.Ins :=
  (List.range convOffs.length).flatMap fun i =>
    Lvm.Q1.mul2I (c2Ext (C.getD i default))
      (.ext ⟨.K, b + 2 * convOffs.getD i 0, [2]⟩, .ext ⟨.K, b + 2 * convOffs.getD i 0 + 1, [2]⟩)
      (if i = 0 then c2Ext z0 else Lvm.Q1.locS2 (2 * (i - 1)))

/-- **The slot weights of a block of `nl` lanes** at the slot point `τ` (5 values): `W_z(τ) = Σ_{l<nl} eq(τ, l)·
ω(64 l + z)`, `z < 64`, as `Σ_o C_o·eZ[(z + o) mod 64]`: the coefficients straight, the 64 sums one loop over
`z` (`convIns`) on a doubled copy of `eZ`. -/
def slotWeightsU (z one : C2) (B eZ τ : List C2) (nl : Nat) : BM (List C2) :=
  g2EqTab z [one] τ >>= fun et =>
  -- `E_x = Σ_{l < nl, l mod 5 = x} eq(τ, l)`
  mapB (fun x => g2Sum z (((List.range nl).filter fun l => l % 5 = x).map fun l => et.getD l default))
    (List.range 5) >>= fun E =>
  -- lane `m`'s two coefficients
  mapB (fun m =>
    (if m < nl then g2Add (et.getD m default) (E.getD ((m + 4) % 5) default)
     else pure (E.getD ((m + 4) % 5) default)) >>= fun c1 =>
    g2Mul (B.getD (keccakPi m) default) c1 z >>= fun u1 =>
    g2Mul (B.getD (keccakPi m) default) (E.getD ((m + 1) % 5) default) z >>= fun u2 =>
    pure (u1, u2)) (List.range 25) >>= fun us =>
  -- `C_o`
  mapB (fun o => g2Sum z
    (((List.range 25).filter fun m => Lvm.Q1.rho m = o).map (fun m => (us.getD m default).1) ++
      ((List.range 25).filter fun m => (Lvm.Q1.rho m + 1) % 64 = o).map (fun m => (us.getD m default).2)))
    convOffs >>= fun C =>
  -- `eZ ‖ eZ` on 128 consecutive twin pairs (the loop's operand `eZ[(z + o) mod 64]` at stride 2 from `2o`)
  mapB (fun e => g2Lin 0 0 e e) (eZ ++ eZ) >>= fun cp =>
  VF.loopF [6] (Lvm.Q1.tplOf (convIns z C (cp.getD 0 default).re.n)) >>= fun lo =>
  pure ((List.range 64).map fun zz => lo.cell2 (2 * convOffs.length - 2) zz)

/-- **The slot check of a block of `nl` lanes** `gate·(final' + Σ_z W_z(τ)·slice_z) = 0`, the slices at lanes
`qs + 2 z`. -/
def slotWU (qs nl : Nat) (B eZ τ : List C2) (z one final : C2) (gate : Cell) : BM Unit :=
  let sl := slices2 qs
  slotWeightsU z one B eZ τ nl >>= fun W =>
  g2Dot final ((List.range 64).map fun zz => (W.getD zz default, sl.getD zz default)) >>= fun e =>
  g2Assert e gate

/-! ## The phase -/

/-- The lanes of `CHwire` at S2GU from the first message lane `qw` (`w` wiring rounds): the three values, then per
slot reduction its first round's message, its slices and its row switch's first answer. -/
structure WireLanesU where
  /-- `g_D` (then `g_Y`, `g_M` two lanes apart). -/
  g3 : Nat
  slotD : Nat
  slicesD : Nat
  ringD : Nat
  slotY : Nat
  slicesY : Nat
  ringY : Nat
  slotM : Nat
  slicesM : Nat
  ringM : Nat
  /-- The phase's end. -/
  next : Nat

/-- One slot reduction's lanes from its first message lane `q` (`R` rounds): slices, ring, next. -/
def slotLanesU (R q : Nat) : Nat × Nat × Nat :=
  let sl := q + roundLanes2 * R
  (sl, sl + 128, sl + 128 + 63)

/-- **The lanes of `CHwire` at S2GU.** -/
def wireLanesU (w qw : Nat) : WireLanesU :=
  let g3 := qw + roundLanes2 * w
  let d := slotLanesU 2 (g3 + 6)
  let y := slotLanesU 5 d.2.2
  let m := slotLanesU 5 y.2.2
  ⟨g3, g3 + 6, d.1, d.2.1, d.2.2, y.1, y.2.1, y.2.2, m.1, m.2.1, m.2.2⟩

/-- The gadget's outputs. -/
structure WireOutU where
  /-- The wiring point `σ` (`w` values). -/
  sigma : List C2
  /-- The slot points of `D` (2), `Y` (5), `M` (5). -/
  tauD : List C2
  tauY : List C2
  tauM : List C2
  /-- Zero and one. -/
  z : C2
  one : C2

/-- **V's wire at S2GU** without the row switches (`w = 20` rounds from lane `qw`; `cv` the tape's claim at `P = 16`,
`mb` `m`'s bits, `sb` `s'`'s bits, both `K` cells; `B`, `K` the sponge's layout constants; `gate` the node flag). -/
def wireGU (P w qw : Nat) (cv : Nat → C2) (mb sb : List Cell) (B K : Nat) (zk gate : Cell) : BM WireOutU :=
  let L := wireLanesU w qw
  let mb2 := mb.map fun b => kC2 b zk
  let sb2 := sb.map fun b => kC2 b zk
  let mu := (List.range 16).map fun i => cv (1 + i)
  let rho := (List.range (P + 1)).map fun i => cv (18 + i)
  let Bv := (List.range 25).map fun l => cv (19 + P + l)
  preWU P cv mb2 sb2 >>= fun G =>
  sc2 w qw G.target >>= fun sc =>
  let gD := ld2 L.g3
  let gY := ld2 (L.g3 + 2)
  let gM := ld2 (L.g3 + 4)
  kernU G.z G.one rho mu sc.1 mb2 G.lt B K >>= fun k =>
  g2Mul k.kks gY G.z >>= fun t1 => g2Mul k.iks gM t1 >>= fun t2 =>
  g2Mul k.e' t2 sc.2 >>= fun t3 => g2Mul k.kch gD t3 >>= fun fin =>
  g2Assert fin gate >>= fun _ =>
  sc2 2 L.slotD gD >>= fun sd =>
  slotW2 L.slicesD G.om sd.1 G.z G.one sd.2 gate >>= fun _ =>
  sc2 5 L.slotY gY >>= fun sy =>
  slotWU L.slicesY 25 Bv G.eZ sy.1 G.z G.one sy.2 gate >>= fun _ =>
  sc2 5 L.slotM gM >>= fun sm =>
  slotWU L.slicesM 17 Bv G.eZ sm.1 G.z G.one sm.2 gate >>= fun _ =>
  pure ⟨sc.1, sd.1, sy.1, sm.1, G.z, G.one⟩

/-- The ground challenges of `CHwire` at S2GU (`(answer lane, g)`): the wiring rounds and the three slot reductions'. -/
def wireChalsU (w qw : Nat) : List (Nat × Nat) :=
  let L := wireLanesU w qw
  (sc2Ans w qw ++ sc2Ans 2 L.slotD ++ sc2Ans 5 L.slotY ++ sc2Ans 5 L.slotM).map fun q => (q, Lvm.E2V.gC2)

end Lvm.Q2
