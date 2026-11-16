-- New for lvm2 S1 (E2-F, E2F-V): S2GF's middle phases `midF₂` (the successor of roll 11's `midT₂`): the typed
-- phases, then the `E2` front (`kgProgF`: the tape caller, `KS`, the `KS` link), then the claims, `E2` claims split
-- into their two `K`-linear halves in place (re first; NOTE-FIELD Prop 7.1, `wordClaimE2`).
import LvmE2VProgKS
import LvmTypedSpecXD
import LvmScheduleF
import LvmE2VPub

/-!
# S2GF's middle phases

* **`SumE2`**: a claim `Σ_k c_k·sel_k(x)·eq(z_k, x_{<v_k})` on `K` data with `E2` coefficients and points
  (a point claim is one part with `c = 1`); **`splitE2`**: its two block claims over `E3`, weights the
  coordinates of `Σ_k c_k·sel_k(x)·wordW z_k x_{<v_k}` in `Quad Ext3`, values `ofK` of the value's
  coordinates (E2F-P (4): consecutive, re then im).
* `tapeClaimsF`, `keccakClaimsF`, `ksOutputClaimsF`, `ksLinkClaimsF`: `LvmVEqMid`'s claims at `E2`, in the
  same order. The row switches' claims and T5's boundary claims (public binary points) are `E3` claims
  as before (E2F-P (8)).
* `kgProgF`: the tape caller (`w = 20`, `D` at block 0 of two), `KS` (`ksLog = 13`), the `KS` link (`X` on
  `2^9` rows, continuation rows `contRowsF` from S2GF's 4,295 sponge blocks); `assembleSF`, `assembleF₂` (the small
  shape's `onStackZs` after the split, E2F-P (7));
  **`midF₂`**: the typed phases, `kgProgF`, the claims.

The typed phases are E2F-Q's amendment-1 program `typedProgX` (`ω`, 6 values, 8 matrix values, `κ` of 3,
`Φ_Q` on 44 variables); `midFWith` takes the typed program of the statement as a parameter.
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm.VEq (BClaim VPlacement VStackClaim selE dBlkE ksBlk ksY2Off xOff nuMainE hdX pubX)
open Lvm.ASM (OpenClaims)

/-! ## `E2` claims and their split -/

/-- An `E2` sum claim on `C_main`'s words: parts `(c, block, z)`, the value. -/
structure SumE2 where
  /-- The parts: coefficient, block, point on the block's variables. -/
  parts : List (E2 × VPlacement × List E2)
  /-- The claimed value. -/
  value : E2

/-- A point claim `f̃_blk(z) = v`. -/
def pointE2 (blk : VPlacement) (z : List E2) (v : E2) : SumE2 := ⟨[(1, blk, z)], v⟩

/-- **The claim's weight in `Quad Ext3`** at an `E3` point of `nu` coordinates. -/
def sumW6 (parts : List (E2 × VPlacement × List E2)) (x : List E) : E6 :=
  (parts.map fun (c, blk, z) ↦
    e2ToE6 c * Lvm.Quad.C (blk.eqAbove x) * wordW z (x.take blk.variableCount)).sum

/-- **The split**: two block claims on the whole stack (`nu` variables), re then im. -/
def splitE2 (nu : ℕ) (c : SumE2) : List BClaim :=
  [⟨⟨nu, 0⟩, fun x ↦ (sumW6 c.parts x).re, ofK c.value.re⟩,
   ⟨⟨nu, 0⟩, fun x ↦ (sumW6 c.parts x).im, ofK c.value.im⟩]

/-! ## The front's claims at `E2` (`LvmVEqMid`'s, in order) -/

/-- What `kgProgF` returns. -/
abbrev KgOutF : Type := TapeOutE2 × (CallerOutE2 × (List E2 × (List E2 × E2) × List E2))

/-- **The tape's claims** (`tapeClaimsE`): `D̃_l(r) = a_l` (`l < 4`, split), the row claim on `C_main`,
the boundary claims `D̃_l(bits(n − 1)) = h_l` (`E3`). -/
def tapeClaimsF (tp : TapeOutE2) (pub : Lvm.Pub) : List BClaim :=
  ((List.range 4).flatMap fun l ↦ splitE2 nuMainE (pointE2 dBlkE (tp.1 ++ selPtF l 2) (tp.2.1.getD l 0))) ++
  [⟨⟨nuMainE, 0⟩, tp.2.2.2.d.row.2, tp.2.2.2.d.row.1⟩] ++
  (pub.h.zipIdx.map fun (w, l) ↦
    BClaim.point dBlkE (selE (pub.n - 1) 20 ++ selE l 2) (M3.kE w))

/-- `KS`'s claims (`keccakClaimsE`): the committed outputs' word claims (split), the row claim. -/
def keccakClaimsF (blk : VPlacement) (co : CallerOutE2) : List BClaim :=
  co.2.2.1.1.flatMap (fun c ↦ splitE2 nuMainE (pointE2 blk c.point c.value)) ++
    [⟨blk, co.2.2.2.2, co.2.2.2.1⟩]

/-- `KS`'s `Y` lane `l` (`ksYPartE`). -/
def ksYPartF (l : ℕ) (pt : List E2) : VPlacement × List E2 :=
  if l < 14 then (ksBlk, pt ++ selPtF (50 + l) slotLog)
  else (⟨13, ksY2Off + (l - 14) * 2 ^ 13⟩, pt)

/-- The openings of `KS`'s 25 output lanes (`ksOutputClaimsE`), split. -/
def ksOutputClaimsF (rk v : List E2) : List BClaim :=
  (List.range 25).flatMap fun l ↦
    let bz := ksYPartF l rk
    splitE2 nuMainE (pointE2 bz.1 bz.2 (v.getD l 0))

/-- **The `KS` link's claims** (`ksLinkClaimsE`): `[Y, in, M, X]`, each split; `M` on `C_rec`'s rows. -/
def ksLinkClaimsF (kchal : List E2) (kshift : List E2 × E2) (vals : List E2) : List (Lvm.Com × BClaim) :=
  let om := eqKernelF (kchal.drop 13)
  let rho' := kshift.1
  let xlo := rho'.take 9
  let sel := selXF 9 rho'
  let yC : SumE2 := ⟨(List.range 25).map fun l ↦
    let bz := ksYPartF l rho'
    (om.getD l 0, bz.1, bz.2), vals.getD 0 0⟩
  let inC : SumE2 := ⟨(List.range 25).map fun l ↦ (om.getD l 0, ksBlk, rho' ++ selPtF l slotLog),
    vals.getD 1 0⟩
  let mC : SumE2 := ⟨(List.range 17).map (fun l ↦ (om.getD l 0, (⟨13, l * 2 ^ 14⟩ : VPlacement), rho')) ++
    (List.range 17).map (fun l ↦ (om.getD l 0 * sel, (⟨9, l * 2 ^ 14 + ksSplit P20⟩ : VPlacement), xlo)),
    vals.getD 2 0⟩
  let xC : SumE2 := ⟨(List.range 17).map fun l ↦ (om.getD l 0, (⟨9, xOff + l * 2 ^ 14⟩ : VPlacement), xlo),
    vals.getD 3 0⟩
  (splitE2 nuMainE yC).map (.main, ·) ++ (splitE2 nuMainE inC).map (.main, ·) ++
    (splitE2 19 mC).map (.crec, ·) ++ (splitE2 nuMainE xC).map (.main, ·)

/-! ## The phases -/

/-- **The `KS` continuation rows at S2GF** (`contRows` with S2GF's trace: `spongeBlocksF P20F accVF = 4,295`
blocks, not `S2GM`'s 4,447): the trace's continuation rows `1 … blocks − 1` and rows 1–31 of the WOTS leaf. -/
def contRowsF : List ℕ :=
  (List.range (spongeBlocksF P20F accVF - 1)).map (· + 1) ++ (List.range 31).map (ksSplit P20 + 399 + 1 + ·)

/-- **The `E2` front with the `KS` link's continuation rows `rows`** (S2GF's CHtape, CHwire, KS, KSlink). -/
def kgProgFR (rows : List ℕ) (s : RecursionFast.Digest) (n : ℕ) : VerifierProgram KgOutF :=
  tapeProgE2 20 1 0 s n >>= fun tp ↦
    callerProgE2 (9 + 4) >>= fun co ↦ ksLinkProgE2 (9 + 4) 9 rows >>= fun lo ↦
      pure (tp, (co, lo))

/-- **The `E2` front** (S2GF's CHtape, CHwire, KS, KSlink), on S2GF's continuation rows `contRowsF`. -/
def kgProgF (s : RecursionFast.Digest) (n : ℕ) : VerifierProgram KgOutF :=
  kgProgFR contRowsF s n

/-- **The front's claims** per commitment `(C_rec, C_main)` (`assembleS` with no tables). -/
def assembleSF (pub : Lvm.Pub) (kg : KgOutF) : List VStackClaim × List VStackClaim :=
  let ks := kg.2.1
  let claims : List (Lvm.Com × BClaim) :=
    (tapeClaimsF kg.1 pub ++ keccakClaimsF ksBlk ks ++ ksOutputClaimsF ks.1 ks.2.1).map (.main, ·) ++
      ksLinkClaimsF kg.2.2.1 kg.2.2.2.1 kg.2.2.2.2
  let on (com : Lvm.Com) := (claims.filter (·.1 == com)).map (·.2.onStack)
  (on .crec, on .main)

/-- **The typed claims and the front's, in both shapes** (`assembleT₂`): `C_main`'s through `onStackZ` when
small, after the split. -/
def assembleF₂ (x : List UInt8) (a : OpenClaims) (kg : KgOutF) : OpenClaims :=
  (a.1 ++ (assembleSF (pubX x) kg).1, Lvm.Shape.onStackZs x (a.2 ++ (assembleSF (pubX x) kg).2))

/-- The middle phases with the typed program `typed` (of the statement: it reads the stage's public values) and
the `KS` link's continuation rows `rows`. -/
def midFWithR (typed : List UInt8 → VerifierProgram OpenClaims) (rows : List ℕ) (x : List UInt8) :
    VerifierProgram OpenClaims :=
  typed x >>= fun a ↦ kgProgFR rows (hdX x).s (pubX x).n >>= fun k ↦ pure (assembleF₂ x a k)

/-- The middle phases with the typed program `typed` (on `contRowsF`). -/
def midFWith (typed : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) : VerifierProgram OpenClaims :=
  midFWithR typed contRowsF x

/-- **S2GF's middle phases** (the successor of `midT₂`): the coordinate-split typed phases `typedProgX` on S2GF's
public values `pubXF` (`acc_in` of 44 coordinates). -/
def midF₂ (Ti : Lvm.Typed.TInst) : List UInt8 → VerifierProgram OpenClaims :=
  midFWith fun x ↦ Lvm.Typed.typedProgX Ti (Lvm.VEq.pubXF x)

end Lvm.E2V
