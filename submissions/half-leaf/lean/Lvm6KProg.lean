-- New for lvm6 K1: the tree batch's and the sponge batch's Keccak programs on the v6 transcript
-- (`FORMAT6.md` §4, §6.2 rows 1–10, §6.3), in season 1's DSL at `E2`. Frozen with `Lvm6KStmt`
-- (`docs/lvm6/stages/K1-keccak.md`).
import Lvm6KPackLayer

/-!
# The v6 Keccak programs (tree batch and sponge core)

Category B (transcribed from `FORMAT6.md` §6.2, §6.3 and leanVM `fdb317982`'s `verify_keccak`, with
the changes BLUEPRINT §2.3 v3 states). Every item of the schedule is one DSL step:

| `FORMAT6.md` | here |
|---|---|
| `E(k)` | `e2Reads k` (16-byte scalars) |
| `K(k)` | `kReads k` (8-byte words, lane 0 of a read) |
| `G(g)` | `e2Sample g`: the nonce (a read), the draw, `powOK g` (lane 2 `< 2^(64−g)`), lanes 0–1 |
| `D(k)` | `dDraws k`: `k` draws with no read and no proof of work |
| `R(n, g)` | one round of `sumcheckE2 g` / `packRoundsN g` |

There is no separator (`e2Sep`) anywhere: `layer6` is K0's `verifyKeccakLayerE2N` without it.

* `kHead6 P base inst output`: rows 6–9 for a batch of `2^(P+4)` rows: `G(3) D(5)` → `r_seg`,
  `r_lane`; `c_st`; leanVM's first claim (`firstClaimSF Shape.v1`: one weight vector for both
  segments); 12 normalized layers; the middle-state opening on slots `base + ℓ` (6 rounds, `c_out`).
* `treeEnd6 P claim`: row 10 of §6.2, the split input end: the constants off the claim, 4 low row
  bits, the top row bit, 6 slot bits, 64 slices, the check with `W(z)` (byte shift `pw^P`, `pw^L`).
* `spongeEnd6 P claim`: row 10 for the sponge (§6.3): 4 low bits, 6 slot bits, slots `25m + ℓ`.
* `treeProg κ`: §6.2 rows 1–10 (`δ`, `ρ`, `D^b`, `u`, `o₄ … o₂₄`, the reduction).
* `spongeCore6 P inst output`, `spCaller6 h`: the sponge core and season 1's caller around it
  (`h` instance coordinates `G(1)` each, 25 output scalars), the row switch replaced by ring
  switching (the slices are returned).
-/

set_option autoImplicit false

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (Shape)
open Lvm.E2V Lvm6.KPack
open Finset

/-! ## Grinds of the tree groups (`P.groups` 0–2; the layer and round grinds are S1's `gC*`) -/

/-- The wiring point `ρ` (numerator 18). -/
abbrev gRho : ℕ := 5
/-- The fold challenge `u` (numerator 1). -/
abbrev gU : ℕ := 1
/-- The segment and lane point `(r_seg, r_lane)` (numerator 6). -/
abbrev gSeg : ℕ := 3

/-! ## Transcript items -/

/-- **A `K` word** (8 bytes, `K(1)`): lane 0 of a read. -/
def kRead : VerifierProgram K := VerifierProgram.readScalar >>= fun x ↦ pure (x.limb 0)

/-- `n` `K` words. -/
def kReads : ℕ → VerifierProgram (List K)
  | 0 => pure []
  | n + 1 => kRead >>= fun x ↦ kReads n >>= fun xs ↦ pure (x :: xs)

/-- **A further draw** (`D(1)`): one draw, no nonce, no proof of work; lanes 0–1. -/
def dDraw : VerifierProgram E2 := VerifierProgram.sampleChallenge >>= fun c ↦ pure (e2OfE c)

/-- `n` further draws. -/
def dDraws : ℕ → VerifierProgram (List E2)
  | 0 => pure []
  | n + 1 => dDraw >>= fun x ↦ dDraws n >>= fun xs ↦ pure (x :: xs)

/-- **A ground group with further draws** (`G(g) D(n)`): `n + 1` coordinates, one nonce. -/
def gPoint (g n : ℕ) : VerifierProgram (List E2) :=
  e2Sample g >>= fun c ↦ dDraws n >>= fun cs ↦ pure (c :: cs)

/-! ## The layers (`verify_layer`, normalized, no separator) -/

/-- **One layer** (§6.2 row 8): `E(47)`, the product check, `G(6)` → `s`, the eq-mode rounds over
the point, 11 plain position rounds, `E(3)`, the final check, `G(2)` → `β`. -/
def layer6 (logSteps step : ℕ) (claim : KClaim E2) : VerifierProgram (KClaim E2) :=
  e2Reads productBits >>= fun product ↦
  VerifierProgram.require (projectedF claim product + iotaSF Shape.v1 logSteps step claim *
    sumF claim.mu = claim.value) >>= fun _ ↦
  e2Sample gC46 >>= fun s ↦
  packRoundsN gC3 claim.point (polyEvalF product s) >>= fun vp ↦
  sumcheckE2 gC3 vp.1 4 (List.replicate keccakLocalBits none) >>= fun lv ↦
  layerTailE2N claim s vp.2 lv

/-- The layers `steps`, in order. -/
def layers6 (logSteps : ℕ) : List ℕ → KClaim E2 → VerifierProgram (KClaim E2)
  | [], claim => pure claim
  | step :: steps, claim => layer6 logSteps step claim >>= fun c ↦ layers6 logSteps steps c

/-! ## The weights (closed forms) -/

/-- The middle-state opening's weight at the slot point `ϱ` (`open(first, 1, 1, c_st)` with slot
`base + ℓ`): `(1 + r_seg)·Σ_ℓ eq(ϱ, base + ℓ)·eq(r_lane, ℓ)`. -/
def midWt (base : ℕ) (rseg : E2) (rlane ϱ : List E2) : E2 :=
  (1 + rseg) * ∑ l ∈ range 25, eqAtF ϱ (base + l) * eqAtF rlane l

/-- The sponge input end's weight of slice `z` at the slot point `ϱs` (slots `25m + ℓ`):
`Σ_m eq(r'_seg, m)·Σ_ℓ eq(ϱs, 25m + ℓ)·w_{64ℓ+z}`. -/
def spWt (rseg : E2) (w ϱs : List E2) (z : ℕ) : E2 :=
  ∑ m ∈ range 2, eqAtF [rseg] m * ∑ l ∈ range 25, eqAtF ϱs (25 * m + l) * w.getD (64 * l + z) 0

/-- The byte-shift pull-back of slot `o`'s bit `z` (`Sh`): the input bit it lands on is bit
`z + 8` of lane `o` (`z < 56`) or bit `z − 56` of lane `o + 1`. -/
def shW (w : List E2) (o z : ℕ) : E2 :=
  if z < 56 then w.getD (64 * o + z + 8) 0 else w.getD (64 * (o + 1) + z - 56) 0

/-- `pw^L(o, z)`: the leaf map's pull-back (slots `0 … 3`). -/
def pwL (w : List E2) (o z : ℕ) : E2 := if o < 4 then shW w o z else 0

/-- `pw^P(o, z)`: the parent map's pull-back (slots `0 … 7`, the same formula in `o`, N2). -/
def pwP (w : List E2) (o z : ℕ) : E2 := if o < 8 then shW w o z else 0

/-- `pw^M(o, z)`: the middle state (slots `8 … 32`), unshifted. -/
def pwM (w : List E2) (o z : ℕ) : E2 := if 8 ≤ o ∧ o < 33 then w.getD (64 * (o - 8) + z) 0 else 0

/-- The set bits of the parent constants `c^P` (`0x44`, pad at byte 65, `0x80` at byte 135). -/
def cPbits : List ℕ := [2, 6, 520, 1087]

/-- The set bits of the leaf constants `c^L` (`0x48`, pad at byte 33, `0x80` at byte 135). -/
def cLbits : List ℕ := [3, 6, 264, 1087]

/-- `C^t = Σ_j w_j` over the set bits of `c_t`. -/
def cW (w : List E2) (bits : List ℕ) : E2 := (bits.map fun j ↦ w.getD j 0).sum

/-- **The tree input end's weight** of slice `z` (BLUEPRINT §2.3 step 6, `FORMAT6.md` §6.2
row 10): `Σ_o eq(ϱ_slot, o)·[(1+r'_seg)·((1+r_top)(1+ϱ_top)·pw^P + r_top·ϱ_top·pw^L)
+ r'_seg·eq(r_top, ϱ_top)·pw^M]`. -/
def treeWt (rseg rtop ϱtop : E2) (w ϱs : List E2) (z : ℕ) : E2 :=
  ∑ o ∈ range 64, eqAtF ϱs o *
    ((1 + rseg) * ((1 + rtop) * (1 + ϱtop) * pwP w o z + rtop * ϱtop * pwL w o z) +
      rseg * (1 + rtop + ϱtop) * pwM w o z)

/-! ## The reduction -/

/-- What the head of a reduction returns: `r_seg :: r_lane`, `c_st`, the claim after the layers,
the middle-state opening's slot point and word `c_out`. -/
structure HeadOut where
  /-- `r_seg :: r_lane` (6 coordinates). -/
  sl : List E2
  /-- The committed share `c_st`. -/
  cst : E2
  /-- The claim after the 12 layers. -/
  claim : KClaim E2
  /-- The middle-state opening's slot point (6 coordinates). -/
  ϱm : List E2
  /-- The middle-state word `c_out`. -/
  cout : E2

/-- **Rows 6–9** for a batch of `2^(P+4)` rows at the instance point `inst` with the output
lanes `output`: `G(3) D(5)`, `c_st`, the first claim, 12 layers, the middle-state opening on
slots `base + ℓ`. -/
def kHead6 (P base : ℕ) (inst output : List E2) : VerifierProgram HeadOut :=
  gPoint gSeg 5 >>= fun sl ↦
  e2Read >>= fun cst ↦
  layers6 (P + 4) (List.range 12)
    (firstClaimSF Shape.v1 inst (sl.take 1) (sl.drop 1) output cst) >>= fun claim ↦
  sumcheckE2 gC2 cst 3 (List.replicate 6 none) >>= fun om ↦
  e2Read >>= fun cout ↦
  VerifierProgram.require (midWt base (sl.headD 0) (sl.drop 1) om.1 * cout = om.2) >>= fun _ ↦
  pure ⟨sl, cst, claim, om.1, cout⟩

/-- What an input end returns: the opening's sumcheck point, the slice point, the 64 slices. -/
structure EndOut where
  /-- The input opening's challenges (11 for the tree, 10 for the sponge). -/
  ϱ : List E2
  /-- The point of the 64 slice claims (`P + 4 + 6` coordinates). -/
  pt : List E2
  /-- The slices `s₀ … s₆₃`. -/
  s : List E2

/-- The claim value after the constants come off (`value'`, §6.2 row 10). -/
def treeV' (P : ℕ) (claim : KClaim E2) : E2 :=
  claim.value + (1 + claim.point.getD P 0) * claim.mu.sum *
    ((1 + claim.point.getD (P - 1) 0) * cW claim.weights cPbits +
      claim.point.getD (P - 1) 0 * cW claim.weights cLbits)

/-- **The tree's input end** (§6.2 row 10): the constants off, 11 plain rounds (4 low row bits,
the top row bit, 6 slot bits), 64 slices, the final check. `r'_seg = point[P]` (N1),
`r_top = point[P − 1]`. -/
def treeEnd6 (P : ℕ) (claim : KClaim E2) : VerifierProgram EndOut :=
  sumcheckE2 gC2 (treeV' P claim) 3 (List.replicate 11 none) >>= fun lv ↦
  e2Reads 64 >>= fun s ↦
  VerifierProgram.require (multilinearEvalF claim.mu (lv.1.take 4) *
    ∑ z ∈ range 64, treeWt (claim.point.getD P 0) (claim.point.getD (P - 1) 0) (lv.1.getD 4 0)
      claim.weights (lv.1.drop 5) z * s.getD z 0 = lv.2) >>= fun _ ↦
  pure ⟨lv.1, lv.1.take 4 ++ claim.point.take (P - 1) ++ [lv.1.getD 4 0] ++ lv.1.drop 5, s⟩

/-- **The sponge's input end** (§6.3): 10 plain rounds (4 low bits, 6 slot bits), 64 slices, the
final check over slots `25m + ℓ`. -/
def spongeEnd6 (P : ℕ) (claim : KClaim E2) : VerifierProgram EndOut :=
  sumcheckE2 gC2 claim.value 3 (List.replicate 10 none) >>= fun lv ↦
  e2Reads 64 >>= fun s ↦
  VerifierProgram.require (multilinearEvalF claim.mu (lv.1.take 4) *
    ∑ z ∈ range 64, spWt (claim.point.getD P 0) claim.weights (lv.1.drop 4) z * s.getD z 0 =
      lv.2) >>= fun _ ↦
  pure ⟨lv.1, lv.1.take 4 ++ claim.point.take P ++ lv.1.drop 4, s⟩

/-! ## The tree batch (§6.2) -/

/-- What the tree batch returns. -/
structure TreeOut where
  /-- `δ₀ … δ₃` (row 1). -/
  δ : List K
  /-- `ρ ∈ E^(κ−1)` (row 2). -/
  ρ : List E2
  /-- `D⁰₀ … D⁰₃, D¹₀ … D¹₃` (row 3). -/
  dd : List E2
  /-- `u` (row 4). -/
  u : E2
  /-- `o₀ … o₂₄`: `o_m = (1+u)·D⁰_m + u·D¹_m` for `m < 4`, then row 5's `o₄ … o₂₄`. -/
  o : List E2
  /-- Rows 6–9. -/
  hd : HeadOut
  /-- Row 10. -/
  en : EndOut

/-- `o_m = (1+u)·D⁰_m + u·D¹_m`, `m < 4` (row 4). -/
def oLow (u : E2) (dd : List E2) : List E2 :=
  (List.range 4).map fun m ↦ (1 + u) * dd.getD m 0 + u * dd.getD (4 + m) 0

/-- **The tree batch** for `2^κ` heap rows (`κ = logN + 1`; `FORMAT6.md` §6.2 rows 1–10). -/
def treeProg (κ : ℕ) : VerifierProgram TreeOut :=
  kReads 4 >>= fun δ ↦
  gPoint gRho (κ - 2) >>= fun ρ ↦
  e2Reads 8 >>= fun dd ↦
  e2Sample gU >>= fun u ↦
  e2Reads 21 >>= fun o' ↦
  kHead6 (κ - 4) 8 (u :: ρ) (oLow u dd ++ o') >>= fun hd ↦
  treeEnd6 (κ - 4) hd.claim >>= fun en ↦
  pure ⟨δ, ρ, dd, u, oLow u dd ++ o', hd, en⟩

/-! ## The sponge batch (§6.3; caller and link: §T, season 1's) -/

/-- **The sponge core** (§6.3): rows 6–10 with leanVM's slots `25m + ℓ`. -/
def spongeCore6 (P : ℕ) (inst output : List E2) : VerifierProgram (HeadOut × EndOut) :=
  kHead6 P 25 inst output >>= fun hd ↦ spongeEnd6 P hd.claim >>= fun en ↦ pure (hd, en)

/-- What the sponge caller returns: `r`, the 25 output scalars, the core's output. -/
abbrev SpOut : Type := List E2 × List E2 × (HeadOut × EndOut)

/-- **The sponge caller** (season 1's `callerProgE2` around the v6 core): `h` instance
coordinates (`G(1)` each), 25 scalars, the core; the slices go to ring switching. -/
def spCaller6 (h : ℕ) : VerifierProgram SpOut :=
  e2Samples gC1 h >>= fun r ↦
  e2Reads 25 >>= fun v ↦
  spongeCore6 (h - 4) r v >>= fun res ↦
  pure (r, v, res)

end Lvm6.K
