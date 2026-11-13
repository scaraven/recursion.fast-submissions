import LvmDecideM3
import LvmSchedule
import LvmLayout
import LvmKS14Layout

/-!
# The decision `F`: the layout and the links of the M3 instance (`M3.ofParts`)

The layout and the `CH`/`KS` links of WP-15a's protocol (`docs/lvm/stages/WP-15a.md`), normative
since WP-8 proved them (BLUEPRINT §11 A17). `M3.ofParts p bus tables claims check` is the M3
instance with these and the given bus and table parts; the instance of `V_S` is
`M3.real p tabs = M3.ofParts p (busFinalR …) …` (`LvmDecideM3Real`, WP-9, INT-2). The earlier
null instance `M3.v0` (no flush, no table constraint) is gone (INT-2).

**Layout** (offsets in `K` words; `layout0`).
* `P20` (`ν_main = logN + 6`): `CH` block at 0 (`in` slots 0–24, `mid` 25–49, `Y` lanes 0–3 at
  slots 52–55, a 4-aligned subcube); `KS` block at `50 · 2^logN` (`CH` slots 50–51; `KS` `in`
  0–24, `mid` 25–49, `Y` lanes 0–13 at `KS` slots 50–63); `KS` `Y` lanes `14 + c` at
  `56 · 2^logN + c · 2^ksLog`; `X_l` at `56 · 2^logN + 2^(ksLog+4) + l · 2^recRowsLog`.
* `P8` (larger `C_main`): `KS` block at 0, `CH` block at `2^(ksLog+6)`, `KS` `Y` lanes 14–24 at
  `2^(ksLog+7) + c · 2^ksLog`, `X_l` at `2^(ksLog+7) + 2^(ksLog+4) + l · 2^recRowsLog`.
* `C_rec`: column `c` at `c · 2^recRowsLog`: `M_l` (`l < 17`) columns 0–16, `σ'` column 17.

**`CH` link** (`chal = ρ (logN) ‖ λ (3) ‖ ζ (6)`; `ω(l, p) = eq(λ, l) · eq(ζ, p)`, `l < 8`,
`p < 64`). `Pad43` sends bit `q` of `Y` lane `m` to bit `q + 8` of `in` lane `m` (`q ≤ 55`) or bit
`q − 56` of lane `m + 1`: `W(m, q) = ω(m, q + 8)` or `ω(m + 1, q − 56)`; the constant bits are
`C = Σ_{p<8} ω(0, p) bit_p(0x43) + ω(4, 8)`. One sumcheck over the row `k` of
`S(ρ, k) g(k) + Eq'(ρ, k) h_Y(k)` with claim `C (1 + eq(ρ, 1^logN))`, where
`S(ρ, k) = Σ_{i ≤ N−2} eq(ρ, i) [k = i + 1]` (the non-cyclic shift, `shiftEval`) and
`Eq'(ρ, k) = eq(ρ, k) + eq(ρ, 1^n) eq(1^n, k)` (row `N − 1` masked). Its final `f₁` at `ρ'`
becomes, with the 64 `in` slices at `(ρ', λ, 0, 0, 0)`, the claim
`f₁ + S(ρ, ρ') Σ_p eq(ζ, p) inS_p` of a two-round sumcheck over the `Y` lane `m`, ending at `μ`
with `f₂ = Eq'(ρ, ρ') Σ_q W̃(μ, q) yS_q`, the `Y` slices at `(ρ', μ, 1, 0, 1, 1)` (slot `52 + m`).
Claims: the two ring switches at those points, and the constant lanes `in_l = c_l`
(`l = 8 … 24`; `c_16 = 0x80 << 56`) at `(ρ', slot l)`.

**`KS` link** (`kchal = ρ (ksLog) ‖ λ (5)`; `ω_l = eq(λ, l)`). For every row,
`in_i[l] = cont_i Y_{i−1}[l] + [l < 17] Msg_l[i]` (`cont_0 = 0`). One sumcheck with claim `0` of
`Sc(ρ, k) Y_ω(k) + eq(ρ, k) (in_ω(k) + Msg_ω(k))`, `Sc(ρ, k) = eq(ρ, k + 1) cont_{k+1}`,
`Msg_l[k] = M_l[k]` below the split `S = ksSplit p` and `X_l[k − S]` from it (`X`: 17 columns of
`2^xl` rows, `xl = ksXLog p`); the rows from `S` are the subcube with coordinates `xl … ksLog − 1` all one,
selector `sel(x) = Π_{j ≥ xl} x_j`. At `ρ'` the four scalars `Y_ω, in_ω, M_ω, X_ω` and the check
`f = Sc(ρ, ρ') Y_ω + eq(ρ, ρ')(in_ω + M_ω + sel(ρ') X_ω)`, `M_ω` the claim on `M`'s rows below `S`
(KS14, `ksLog ≤ recRowsLog`, `P20`: `M_l`'s extension at `ρ'` plus `sel(ρ')` times its top `2^xl` rows' at
`ρ'_{<xl}`; lvm2 CR-K) or, in v1's layout (`ksLog = recRowsLog + 1`, `P8`: `S = 2^recRowsLog`, `sel = ρ'_r`),
`M_l(ρ'_lo)` scaled by `1 + ρ'_r` in the check. `cont` is 1 on the trace rows `1 … B − 1`
(`B = spongeBlocks`) and on rows 1–31 of the WOTS leaf group (`KS` rows from `S`: 399 chain steps, 32 leaf
rows, 16 path rows, `leafStmt`, `nodeStmt`). `Sc(ρ, ρ')` is summed over the `cont` rows from two `eq` tables.
-/

set_option autoImplicit false

namespace Lvm

/-- Offsets in `C_main` (in `K` words) of the fixed blocks (lvm2 FRZ-0's layout). -/
structure Layout0 where
  /-- The digest column `D`'s block (lvm2 S2: `D_l[i]` at `ch + l · 2^logN`, `l < 4`). -/
  ch : Nat
  /-- `KS`'s block. -/
  ks : Nat
  /-- `KS`'s `Y` lanes 14–24. -/
  ksY2 : Nat
  /-- The `X` message columns. -/
  x : Nat
  /-- The first word past the fixed blocks (`free_lo`). -/
  freeLo : Nat
  /-- The typed committed region `T` (lvm2 roll 8, B1: `z`'s committed words, `2^tLog` from here). -/
  t : Nat
  deriving DecidableEq, Repr

/-- The fixed blocks' sizes as logs, in the tie order `D`, `KS`, `KSY2`, `X`: `D` is 4 lanes of
`2^logN` rows, `KS` 64 slots of `2^ksLog`, `KSY2` 16 slots of `2^ksLog`, `X` 32 columns of
`2^recRowsLog`; with KS14/KS13 (`ksLog ≤ recRowsLog`, lvm2 CR-G0) `X` is 17 columns of `2^(ksLog − 4)` (the messages of
`KS` rows `≥ 2^ksLog − 2^(ksLog − 4)`) in a `2^(ksLog + 1)` block. -/
def layoutLogs (p : Params) : List Nat :=
  [p.logN + 2, p.ksLog + slotLog, p.ksLog + 4, if p.ksLog ≤ p.recRowsLog then p.ksLog + 1 else p.recRowsLog + 5]

/-- `log₂` of the typed committed region `T` (lvm2 roll 8, B1: B1-K's layout's `comLog`, `2^xVars` words). -/
abbrev tLog : Nat := 20

/-- The offset of block `i` under FRZ-0's rule: the blocks placed largest first from word 0 (ties
in the order of `layoutLogs`), so each is aligned to its size. -/
def layoutOff (logs : List Nat) (i : Nat) : Nat :=
  let s := logs.getD i 0
  ((List.range logs.length).filter fun j =>
    decide (s < logs.getD j 0) || (logs.getD j 0 == s && decide (j < i))).foldl
    (fun acc j => acc + 2 ^ logs.getD j 0) 0

/-- The blocks above `D` (lvm2 roll 8, B1): `T`, `KS`, `KSY2`, `X`. -/
def upperLogs (p : Params) : List Nat := tLog :: (layoutLogs p).tail

/-- **The layout of a parameter set** (lvm2 roll 8, B1-IX's rule; FRZ-0's above `D`): `D` at word 0; `T`, `KS`,
`KSY2`, `X` largest first (ties in that order) from `2^22`, the big shape's `D` extent, so that `T` and the `KS`
aliases lie in the small shape's room `[4·2^20, 7·2^20)` (`TypedV.TNat.okB`); `free_lo` the end of the last
block. At `P20` (KS13): `D` 0, `T` `4·2^20`, `KS` `5·2^20`, `KSY2` `5·2^20 + 2^19`, `X` `5·2^20 + 2^19 + 2^17`,
`free_lo` 5,914,624; at `P8`: `D` 0, `T` `4·2^20`, `KS` `5·2^20`, `KSY2` `6·2^20`, `X` `6·2^20 + 2^18`,
`free_lo` 6,815,744 (`layout0_P20`, `layout0_P8`). -/
def layout0 (p : Params) : Layout0 :=
  let U := upperLogs p
  ⟨0, 2 ^ 22 + layoutOff U 1, 2 ^ 22 + layoutOff U 2, 2 ^ 22 + layoutOff U 3,
    2 ^ 22 + (U.map (2 ^ ·)).foldl (· + ·) 0, 2 ^ 22 + layoutOff U 0⟩

/-- The rule's layout at `P20` is the shared one (`LvmLayout`, generated from `params.py`). -/
theorem layout0_P20 : layout0 P20 =
    ⟨CMain.dOff20, CMain.ksOff20, CMain.ksY2Off20, CMain.xOff20, CMain.freeLo20, CMain.tOff20⟩ := by
  decide +kernel

/-- The rule's layout at `P8` is the shared one. -/
theorem layout0_P8 :
    layout0 P8 = ⟨CMain.dOff8, CMain.ksOff8, CMain.ksY2Off8, CMain.xOff8, CMain.freeLo8, CMain.tOff8⟩ := by
  decide +kernel

/-- **`D`'s block** (lvm2 BLUEPRINT2 §1.1, FRZ-0): `4 · 2^logN` words, lane `l` of row `i` at word
`i + 2^logN · l`; a point on it is the `logN` row coordinates, then the 2 lane bits. -/
def dBlock (p : Params) : Placement := ⟨p.logN + 2, (layout0 p).ch⟩

/-- `eq(x, 1^n)`. -/
def eqOnes (x : List FE) : FE := prodE x

/-- `S(x, y) = Σ_{i ≤ N−2} eq(x, i) eq(y, i + 1)`, little-endian: the carry stops at bit `j`. -/
def shiftEval (x y : List FE) : FE :=
  let n := x.length
  sumE ((List.range n).map fun j =>
    prodE ((List.range j).map fun t => x.getD t 0 * (1 + y.getD t 0)) *
      ((1 + x.getD j 0) * y.getD j 0) *
      prodE ((List.range (n - j - 1)).map fun u =>
        1 + x.getD (j + 1 + u) 0 + y.getD (j + 1 + u) 0))

/-- `Eq'(x, y) = eq(x, y) + eq(x, 1^n) eq(1^n, y)`: `eq` with the last row masked. -/
def eqMasked (x y : List FE) : FE := eqEval x y + eqOnes x * eqOnes y

/-- A claim made of several point claims on one commitment of `nu` variables:
`Σ_j c_j · [block_j's extension at z_j]`, as one weight on the whole cube. -/
def sumClaim (nu : Nat) (parts : List (FE × Placement × List FE)) (value : FE) : BlockClaim :=
  ⟨⟨nu, 0⟩, fun x => sumE (parts.map fun (c, blk, z) =>
    c * blk.eqAbove x * eqEval z (x.take blk.variableCount)), value⟩

/-! ## The `CH` link -/

/-- The split of the `CH` link's challenges: `ρ`, `λ`, `ζ`. -/
def chSplit (p : Params) (chal : List FE) : List FE × List FE × List FE :=
  (chal.take p.logN, (chal.drop p.logN).take 3, chal.drop (p.logN + 3))

/-- `ω(l, p)` as a table: row `l < 8`, column `p < 64`. -/
def omegaCH (lam zeta : List FE) : Array (Array FE) :=
  let eL := eqKernelA lam
  let eZ := eqKernelA zeta
  eL.map fun a => eZ.map (a * ·)

/-- `W(m, q)`, the weight of bit `q` of `Y` lane `m` through `Pad43`. -/
def padWeight (om : Array (Array FE)) (m q : Nat) : FE :=
  if q ≤ 55 then (om.getD m #[]).getD (q + 8) 0 else (om.getD (m + 1) #[]).getD (q - 56) 0

/-- The constant bits of `Pad43`'s lanes 0–7: `0x43` in byte 0, `0x01` in byte 33. -/
def padConst (om : Array (Array FE)) : FE :=
  sumE ((List.range 8).filterMap fun p =>
    if (0x43 : Nat).testBit p then some ((om.getD 0 #[]).getD p 0) else none) +
    (om.getD 4 #[]).getD 8 0

/-- The shift sumcheck's claim `C (1 + eq(ρ, 1^logN))`. -/
def chShiftTarget0 (p : Params) (chal : List FE) : FE :=
  let (rho, lam, zeta) := chSplit p chal
  padConst (omegaCH lam zeta) * (1 + eqOnes rho)

/-- The two-round sumcheck's claim `f₁ + S(ρ, ρ') Σ_p eq(ζ, p) inS_p`. -/
def chSc2Target0 (p : Params) (chal : List FE) (shift : List FE × FE) (inS : List FE) : FE :=
  let (rho, _, zeta) := chSplit p chal
  shift.2 + shiftEval rho shift.1 * dot (eqKernel zeta) inS

/-- The `CH` link's check and claims. -/
def chLink0 (p : Params) (blk : Placement) (ySlot : Nat) (i : ChLinkIn) : Bool × List (Com × BlockClaim) :=
  let (rho, lam, zeta) := chSplit p i.chal
  let om := omegaCH lam zeta
  let rho' := i.shift.1
  let mu := i.sc2.1
  let eMu := eqKernel mu
  let wt (q : Nat) : FE := sumE ((List.range 4).map fun m => eMu.getD m 0 * padWeight om m q)
  let ok := i.sc2.2 == eqMasked rho rho' * sumE ((List.range 64).map fun q => wt q * i.ySlices.getD q 0)
  let inPt := rho' ++ lam ++ [0, 0, 0]
  let yPt := rho' ++ mu ++ selectorPoint (ySlot >>> 2) (slotLog - 2)
  let ring (pt : List FE) (r : FE × List FE) : BlockClaim := ⟨blk, fun x => ringWeight pt x r.2, r.1⟩
  let consts := (List.range 17).map fun j =>
    let l := 8 + j
    BlockClaim.point blk (rho' ++ selectorPoint l slotLog)
      (FE.ofK (if l = 16 then ⟨(0x80 : UInt64) <<< 56⟩ else 0))
  (ok, ([ring inPt i.ringIn, ring yPt i.ringY] ++ consts).map (.main, ·))

/-! ## The `KS` link -/

/-- `KS`'s `Y` lane `l` as a placement (`ksLog` variables, or the block's slot). -/
def ksYPart (p : Params) (L : Layout0) (l : Nat) (pt : List FE) : Placement × List FE :=
  if l < 14 then (⟨p.ksLog + slotLog, L.ks⟩, pt ++ selectorPoint (50 + l) slotLog)
  else (⟨p.ksLog, L.ksY2 + (l - 14) * 2 ^ p.ksLog⟩, pt)

/-- The rows where `cont = 1`: the trace's continuation rows and rows 1–31 of the WOTS leaf (the WOTS group
starts at the split, lvm2 CR-K). -/
def contRows (p : Params) : List Nat :=
  (List.range (spongeBlocks p - 1)).map (· + 1) ++
    (List.range 31).map (ksSplit p + 399 + 1 + ·)

/-- `Sc(ρ, ρ') = Σ_{i : cont_i = 1} eq(ρ, i) eq(ρ', i − 1)`. -/
def contShift (p : Params) (rho rho' : List FE) : FE :=
  let e := eqKernelA rho
  let e' := eqKernelA rho'
  (contRows p).foldl (fun acc i => acc + e.getD i 0 * e'.getD (i - 1) 0) 0

/-- The `KS` link's check and claims in v1's layout (`ksLog = recRowsLog + 1`: `P8`). -/
def ksLinkV1 (p : Params) (i : KsLinkIn) : Bool × List (Com × BlockClaim) :=
  let L := layout0 p
  let rho := i.chal.take p.ksLog
  let om := eqKernel (i.chal.drop p.ksLog)
  let rho' := i.shift.1
  let lo := rho'.take p.recRowsLog
  let xr := rho'.getD p.recRowsLog 0
  let y := i.vals.getD 0 0
  let inv := i.vals.getD 1 0
  let mv := i.vals.getD 2 0
  let xv := i.vals.getD 3 0
  let ok := i.shift.2 == contShift p rho rho' * y + eqEval rho rho' * (inv + (1 + xr) * mv + xr * xv)
  let lanes25 := List.range 25
  let lanes17 := List.range 17
  let yC := sumClaim p.nuMain (lanes25.map fun l =>
    let (b, z) := ksYPart p L l rho'
    (om.getD l 0, b, z)) y
  let inC := sumClaim p.nuMain (lanes25.map fun l =>
    (om.getD l 0, (⟨p.ksLog + slotLog, L.ks⟩ : Placement), rho' ++ selectorPoint l slotLog)) inv
  let mC := sumClaim p.nuRec (lanes17.map fun l =>
    (om.getD l 0, (⟨p.recRowsLog, l * 2 ^ p.recRowsLog⟩ : Placement), lo)) mv
  let xC := sumClaim p.nuMain (lanes17.map fun l =>
    (om.getD l 0, (⟨p.recRowsLog, L.x + l * 2 ^ p.recRowsLog⟩ : Placement), lo)) xv
  (ok, [(.main, yC), (.main, inC), (.crec, mC), (.main, xC)])

/-- The `KS` link's check and claims under KS14 (`ksLog ≤ recRowsLog`: `P20`; lvm2 CR-K): `M`'s claim on the rows
below the split (`l·2^r + k`, `k < S`) as the extension of `M_l`'s first `2^ksLog` rows at `ρ'` plus `sel(ρ')` times
its rows `S …` at `ρ'_{<xl}`; `X`'s at `ρ'_{<xl}`. -/
def ksLink14 (p : Params) (i : KsLinkIn) : Bool × List (Com × BlockClaim) :=
  let L := layout0 p
  let xl := ksXLog p
  let R := 2 ^ p.recRowsLog
  let rho := i.chal.take p.ksLog
  let om := eqKernel (i.chal.drop p.ksLog)
  let rho' := i.shift.1
  let xlo := rho'.take xl
  let sel := prodE (rho'.drop xl)
  let y := i.vals.getD 0 0
  let inv := i.vals.getD 1 0
  let mv := i.vals.getD 2 0
  let xv := i.vals.getD 3 0
  let ok := i.shift.2 == contShift p rho rho' * y + eqEval rho rho' * (inv + mv + sel * xv)
  let lanes25 := List.range 25
  let lanes17 := List.range 17
  let yC := sumClaim p.nuMain (lanes25.map fun l =>
    let (b, z) := ksYPart p L l rho'
    (om.getD l 0, b, z)) y
  let inC := sumClaim p.nuMain (lanes25.map fun l =>
    (om.getD l 0, (⟨p.ksLog + slotLog, L.ks⟩ : Placement), rho' ++ selectorPoint l slotLog)) inv
  let mC := sumClaim p.nuRec (lanes17.map (fun l => (om.getD l 0, (⟨p.ksLog, l * R⟩ : Placement), rho')) ++
    lanes17.map fun l => (om.getD l 0 * sel, (⟨xl, l * R + ksSplit p⟩ : Placement), xlo)) mv
  let xC := sumClaim p.nuMain (lanes17.map fun l =>
    (om.getD l 0, (⟨xl, L.x + l * 2 ^ xl⟩ : Placement), xlo)) xv
  (ok, [(.main, yC), (.main, inC), (.crec, mC), (.main, xC)])

/-- **The `KS` link's check and claims**: KS14's when `ksLog ≤ recRowsLog`, else v1's. -/
def ksLink0 (p : Params) (i : KsLinkIn) : Bool × List (Com × BlockClaim) :=
  if p.ksLog ≤ p.recRowsLog then ksLink14 p i else ksLinkV1 p i

/-- The openings of `KS`'s 25 output lanes at the instance point, in lane order. -/
def ksOutputClaims0 (p : Params) (rk v : List FE) : List (Com × BlockClaim) :=
  (List.range 25).map fun l =>
    let (b, z) := ksYPart p (layout0 p) l rk
    (.main, BlockClaim.point b z (v.getD l 0))

/-! ## The instance -/

/-- v1's `CH` slot of `Y` lane 0 (dead at lvm2 S2, where `D` has its own block; kept for v1's `CH`
link code until the circuit drops it; S2's `LvmLayout` has no `chYSlot`). -/
def chYSlotV1 : Nat := 52 -- layout-lint: allow

/-- **The M3 instance from its bus and table parts**: the v0 layout and WP-15a's links (A17),
`busFinal`, `tables`, `tableClaims`, `fixVals`, `fixSent`, `pubCheck` given (A23). -/
def M3.ofParts (p : Params) (busFinal : BusIn → BusOut) (tables : Pub → List TableSpec)
    (tableClaims : Pub → List (List FE × List FE) → List (Com × BlockClaim))
    (fixVals : Pub → List FE → List FE) (fixSent : Pub → List (List FE × List FE) → List FE)
    (pubCheck : Pub → List (List FE × List FE) → Bool) : M3 :=
  let L := layout0 p
  let ch : Placement := dBlock p
  { chBlock := ch
    ksBlock := ⟨p.ksLog + slotLog, L.ks⟩
    chYSlot := Lvm.chYSlotV1
    busFinal := busFinal
    tables := tables
    tableClaims := tableClaims
    fixVals := fixVals
    fixSent := fixSent
    pubCheck := pubCheck
    chShiftTarget := chShiftTarget0 p
    chSc2Target := chSc2Target0 p
    chLink := chLink0 p ch Lvm.chYSlotV1
    ksOutputClaims := ksOutputClaims0 p
    ksShiftTarget := fun _ => 0
    ksLink := ksLink0 p }

end Lvm
