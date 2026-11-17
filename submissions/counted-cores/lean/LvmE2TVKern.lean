-- New for lvm2 E2-FT (stage S2GT, E2F-T-H1): V_S's typed kernels over any field (roll 11's `LvmTypedV` kernels,
-- generic), for the typed phases at `E2` (`LvmE2TV`, at `F = FE2`).
import LvmTypedV
import LvmE2VBase

/-!
# The typed kernels over a field

Roll 11's native kernels of the typed phases (`LvmTypedV`: `hiW`, `mleK`, `virtEF`, `divKern`, `geKern`,
`relayKernF`), text for text over a field `F` (with `FK`'s words through `algebraMap FK F`), so that S2GT's
V_S computes them at `F = FE2` and their closed forms (`LvmE2TVKernP`) are proved once:

* `hiWG`: a region's `eq` weight above its own bits;
* `mleKG`: the multilinear extension of `K` values at an `F` point (the kernel as an array);
* `virtG`: the natively computed part of `z̃(r_y)` (`PUB`, `1`);
* `divKernG`, `geKernG`: the relayout's two automata; `relayKernG`: the relayout's kernel.
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm Lvm.TypedV

section

variable {F : Type} [Field F]

/-- `eq(a, b)` on one coordinate. -/
@[inline] def eq1G (a : F) (b : Bool) : F := if b then a else 1 + a

/-- A region's `eq` weight above its own bits: `eq(r.drop log, base >>> log)`. -/
def hiWG (r : List F) (log base : Nat) : F := E2V.eqAtF (r.drop log) (base >>> log)

/-- `Σ_{i < 2^log} eq(pt, i) · v(i)` (the multilinear extension of `K` values at an `F` point). -/
def mleKG [Algebra FK F] (log : Nat) (v : Nat → FK) (pt : List F) : F :=
  let k := (E2V.eqKernelF (pt.take log)).toArray
  (List.range (2 ^ log)).foldl (fun acc i => acc + algebraMap FK F (v i) * k.getD i 0) 0

/-- **The natively computed part of `z̃(r_y)`** (`virtEF`): the `PUB` regions (header lanes from `dst`, zero past
them) and the `1` regions (their `eq` weight). -/
def virtG [Algebra FK F] (regs : List NReg) (hdr : Array FK) (ry : List F) : F :=
  regs.foldl (fun acc g => match g.src with
    | .pub => acc + hiWG ry g.log g.base * mleKG g.log (fun i => hdr.getD (g.dst + i) 0) ry
    | .one => acc + hiWG ry g.log g.base
    | _ => acc) 0

/-- **The long-division automaton** (`divKern`) over `F`. -/
def divKernG (p0 log : Nat) (ρ rlo rhi : List F) : F :=
  let ρa := ρ.toArray
  let ra := rlo.toArray
  let step (V : Array F) (k : Nat) : Array F :=
    let free := decide (k < log)
    let bits : List Bool := if free then [false, true] else [p0.testBit k]
    let fac (b q : Bool) : F :=
      (if free then eq1G (ρa.getD k 0) b else 1) * (if k < recRowBits then eq1G (ra.getD k 0) q else if q then 0 else 1)
    let f00 := fac false false
    let f01 := fac false true
    let f10 := fac true false
    let f11 := fac true true
    (List.range sLanes).foldl (fun W rem =>
      let v := V.getD rem 0
      bits.foldl (fun W b =>
        let t := 2 * rem + (if b then 1 else 0)
        let q := decide (sLanes ≤ t)
        let f := if b then (if q then f11 else f10) else (if q then f01 else f00)
        W.modify (if q then t - sLanes else t) (· + v * f)) W) (Array.replicate sLanes 0)
  let V := (List.range posBits).reverse.foldl step ((Array.replicate sLanes (0 : F)).set! 0 1)
  (List.range sLanes).foldl (fun acc rem => acc + V.getD rem 0 * E2V.eqAtF rhi rem) 0

/-- **The comparator** (`geKern`) over `F`: `Σ_{i < 2^log, i ≥ c} eq(ρ, i)·eq(r, i)`. -/
def geKernG (c log : Nat) (ρ r : List F) : F :=
  let ρa := ρ.toArray
  let ra := r.toArray
  let t (k : Nat) (b : Bool) : F := eq1G (ρa.getD k 0) b * eq1G (ra.getD k 0) b
  let st := (List.range log).reverse.foldl (fun (st : F × F) k =>
    let full := t k false + t k true
    if c.testBit k then (st.1 * t k true, st.2 * full) else (st.1 * t k false, st.2 * full + st.1 * t k true))
    ((1 : F), (0 : F))
  st.1 + st.2

/-- **The relayout's kernel** (`relayKernF`) over `F`, on the `S_flat` regions `sregs`. -/
def relayKernG (sregs : List NReg) (ry r : List F) : F :=
  sregs.foldl (fun acc g =>
    let ρ := ry.take g.log
    let idp : F := if g.dst + 2 ^ g.log ≤ sPos then 0
      else E2V.eqAtF (r.drop g.log) (g.dst >>> g.log) * geKernG (sPos - min sPos g.dst) g.log ρ (r.take g.log)
    acc + hiWG ry g.log g.base * (divKernG g.dst g.log ρ (r.take recRowBits) (r.drop recRowBits) + idp)) 0

end

end Lvm.E2T
