-- New for lvm6 (WP C6 of CERT, links 1, 2, 13, 15): the final assembly. The certificate with the `S` branch
-- behind the guard, for either value of the guard, and the deployed submission over top-level constants.
import Lvm6CertG
import Lvm6XDom
import Lvm6VGuard6
import Lvm6WOnly
import Lvm6VS1F
import Lvm6VM2F
import Lvm6VS1W
import Lvm6VS1Drv
import Lvm6VPhiE8

/-!
# The certificate of the lvm6 submission (WP C6)

The submission is `submissionOf (VSF6 B P17) (EX6D (accV (VSF6 B P17)) DD) (extX6 DD)`: the `S` branch is the
fast verifier behind the guard `staticOk6 B`, the extractor specification is C4's domain split `EX6D` and the
program is `extX6 DD`.

* **`certified_ofS`** (link 1, season 1's form), **`certified_off`** (link 2, guard off), **`VSF6_on`** and
  **`VSF6_off`** are in `Lvm6CertG` (PORT17 C1), with the guard split over any extractor (`certified_onG`,
  `certified6_guardG`). Here: **`certified_offD`**, `certified_off` at `EX6D` and `extX6 DD`.
* **`open6XD_Φ6`** (moved here from `Lvm6CertPhasesX`, PORT17 C1): C4's `open6XD` at C3's phase inputs, with
  C5's `Xe` and its extraction map `hX` left as hypotheses.
* **`certified_on`** (guard on): `certified_onG` (C4's `certified_ofD` with C3's `queries_VSasm` and
  `refines6_asm`) at `open6XD_Φ6` and C5's `Xe6`, at `V_S = VSasm (Φ6 B h)`, from `node6V` there.
* **`certified6_guard`**: for any base `B` whose phases satisfy `node6V` when the guard holds, the certificate of
  the guarded submission (`certified6_guardG` at `EX6D · DD` and `extX6 DD`). Off: `VSF6 B P17 = VSoff`. On:
  `VSF6_eqP17` (V1), the guard's branch of `VSspec6`, then `VSasm_Φ6` (C3). **`certified6_tiOf6`**: every `tiOf6 P` (`node6V_Φ6`); **`certified6_base6`**: the deployed
  `base6` (`base6_eq`).
* **Link 15, the compiled verifier** (PORT17 V1: at `P17`): `shV6 = toV P17` and the guard `guard6 = staticOk6 base6` (V1c's
  `Lvm6VGuard6`; the base `B6` of the plan is `base6`) are top-level constants, so the badge evaluates them once
  per process when it loads, never inside a timed check. `VSc6` reads them, with the instance
  `inst6F` (VFIX: `inst6` with the public words read off an array; VS1: in machine words; `inst6F_eq`) and VS1's
  decision `FH` (MUL2: as `FB`, the Keccak reductions, the phases' claims and the opening on `m2B`, `FB_eq`) at
  PHIV8's Φ_Q evaluator `base6.P.eval8` (`PT.eval8_eq`, `FH_eq`), driven by VS1's `VS6H` (`VS6H_eq`);
  `VSc6_eq : VSc6 = VSF6 base6 P17`.
  **`submission6`** runs the verifier as the byte-level twin `VwithT VSc6` behind VS1's kind test (`VwithS`);
  `submission6_eq` rewrites by `VwithS_eq` and `VwithT_eq`. **`certified6 : CertificateR declared6 submission6`**.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.T Lvm.X Lvm.FS Lvm6.V

/-- **`open6XD` at `Φ6`**: C3's phase inputs fill `H`, `HG`, `hPF` and `hw`; what is left is C5's `Xe` with its
extraction map `hX`. -/
theorem open6XD_Φ6 (B : TyBase6) (h : staticOk6 B = true) {VS : Shape → SProg}
    (Xe : ∀ vk, Ext6 (schemeOf (prog6 (Φ6 B h)) P17 vk) (Rel (accV (VS P17) vk))
      (G6 (fun _ q => SP.SGood6 q) (fun x q => Ty.TGood6 (inst6 B h x) q)))
    (hX : ∀ vk, (Xe vk).ext = ExtSpec6 (Whir.I6 P17)) :
    XOpen6D (VS P17) (prog6 (Φ6 B h)) (EX6D (accV (VS P17)) (.seq fillIR (descX6 (LvD FDep) finX)))
      (extX6 (.seq fillIR (descX6 (LvD FDep) finX))) :=
  open6XD (phaseSpecs6 B h) (openGood6 B h) (phasesFollow6 B h) Xe rfl hX

end Lvm6.X

namespace Lvm6.Cert

open RecursionFast Lvm.T Lvm.X LeanVM.Parameters
open RecursionFast.WitnessSending (decode)
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm6.V (TyBase6 staticOk6 inst6 VSF6 VSspec6 Φ6 PT base6 guard6)
open Lvm6.X (EX6D extX6 fillIR descX6 LvD FDep finX)
open scoped NNReal

/-- The extractor's descent at `P17`: the fill, then the levels and the final opening. -/
abbrev DD : XIR := .seq fillIR (descX6 (LvD FDep) finX)

/-- `certified_off` at C4's extractor `EX6D A DD` and the program `extX6 DD`, for every acceptance `A`. -/
theorem certified_offD (A : Digest → Digest → Signed → Bool) :
    CertificateR declared6 (submissionOf W.VSoff (EX6D A DD) (extX6 DD)) :=
  certified_off (X.computes6D A _ X.descOk6_FDep) (X.size_extX6 (X.sizeIR_F FDep)) (X.wBranch6D A _)

/-! ## Link 2: the guard on -/

/-- **The certificate at C3's phases** `Φ6 B h`, from the node theorem there (`Xe6`, C5): `certified_onG` at
`open6XD_Φ6`. -/
theorem certified_on (B : TyBase6) (h : staticOk6 B = true)
    (hN : Stmt.node6V (VSasm (Φ6 B h)) (Node.Asm.rest6 B h) (Node.childOf6 Node.Asm.trOfS Node.Asm.σOfS)
      Node.Asm.σlOfS) :
    CertificateR declared6
      (submissionOf (VSasm (Φ6 B h) P17) (EX6D (accV (VSasm (Φ6 B h) P17)) DD) (extX6 DD)) :=
  certified_onG B h (X.open6XD_Φ6 (VS := VSasm (Φ6 B h)) B h (Xe6 B h hN) (Xe6_ext B h hN))

/-- **The certificate of the guarded submission** (link 2), for either value of the guard, for every base `B`
whose phases satisfy the node theorem when the guard holds. -/
theorem certified6_guard (B : TyBase6)
    (hN : ∀ h : staticOk6 B = true, Stmt.node6V (VSasm (Φ6 B h)) (Node.Asm.rest6 B h)
      (Node.childOf6 Node.Asm.trOfS Node.Asm.σOfS) Node.Asm.σlOfS) :
    CertificateR declared6
      (submissionOf (VSF6 B P17) (EX6D (accV (VSF6 B P17)) DD) (extX6 DD)) :=
  certified6_guardG B (fun A => EX6D A DD) (extX6 DD)
    (fun h => X.open6XD_Φ6 (VS := VSasm (Φ6 B h)) B h (Xe6 B h (hN h)) (Xe6_ext B h (hN h)))
    (fun A => X.computes6D A _ X.descOk6_FDep) (X.size_extX6 (X.sizeIR_F FDep)) (fun A => X.wBranch6D A _)

/-- `certified6_guard` at the base `tiOf6 P` of every class table `P` (`node6V_Φ6`). -/
theorem certified6_tiOf6 (P : PT) :
    CertificateR declared6 (submissionOf (VSF6 (Node.Ti.tiOf6 P) P17)
      (EX6D (accV (VSF6 (Node.Ti.tiOf6 P) P17)) DD) (extX6 DD)) :=
  certified6_guard _ (V.node6V_Φ6 P)

/-- `certified6_guard` at every base equal to some `tiOf6 P`. -/
theorem certified6_of_eq {B : TyBase6} {P : PT} (e : B = Node.Ti.tiOf6 P) :
    CertificateR declared6 (submissionOf (VSF6 B P17) (EX6D (accV (VSF6 B P17)) DD) (extX6 DD)) := by
  subst e
  exact certified6_tiOf6 P

/-- **The certificate at the deployed base `base6`** (`base6_eq`). -/
theorem certified6_base6 :
    CertificateR declared6 (submissionOf (VSF6 base6 P17) (EX6D (accV (VSF6 base6 P17)) DD) (extX6 DD)) :=
  certified6_of_eq V.base6_eq

/-! ## Link 15: the compiled verifier over top-level constants -/

/-- **The verifier's shape at `P17`**, a top-level constant. -/
def shV6 : V.VShape := toV P17

/-! ### VFIX: the public words off an array

`inst6`'s public words `QD.pwOf Ti H y` read the header bytes `H` as a list (`Q.le8`, eight `List.getD` each), so
`virtF`'s 2^10 words walk the list 8 · 2^10 times: ≈ 30 ms of every check. The twins below read the same bytes off
an array; `inst6F = inst6`, so the deployed verifier is extensionally unchanged (`VSc6_eq`). -/

/-- `Q.le8` off an array: the little-endian number of the 8 bytes at `o` (zero beyond the end). -/
def le8A (a : Array UInt8) (o : ℕ) : ℕ := ((List.range 8).map fun t => (a.getD (o + t) 0).toNat * 2 ^ (8 * t)).sum

theorem le8A_toArray (l : List UInt8) (o : ℕ) : le8A l.toArray o = Q.le8 l o := by
  simp only [le8A, Q.le8, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

/-- `QD.pwOf` off an array. -/
def pwOfA (Ti : Ty.TInst6) (a : Array UInt8) (y : ℕ) : Lvm.FK :=
  Lvm.QSig.w64 (le8A a (8 * (y - QD.pubBase Ti))).toUInt64

theorem pwOfA_toArray (Ti : Ty.TInst6) (H : List UInt8) : pwOfA Ti H.toArray = QD.pwOf Ti H := by
  funext y
  simp only [pwOfA, QD.pwOf, le8A_toArray]

/-! ### VS1: the public words in machine words, `pubBase` once

`le8A` builds each word as a `Nat` through `2 ^ (8 t)` (GMP's `lean_nat_pow`, eight a word), and `pwOfA` recomputes
`QD.pubBase` (a `find?` over the layout's regions) for every word. `le8W` assembles the word in `UInt64` arithmetic
(`le8W_eq`: it is `le8A`'s word), and `pwOfW` takes the base as an argument, computed once per instance. -/

/-- `le8A`'s word in `UInt64` arithmetic. -/
def le8W (a : Array UInt8) (o : ℕ) : UInt64 :=
  (a.getD o 0).toUInt64 + (a.getD (o + 1) 0).toUInt64 * 0x100 + (a.getD (o + 2) 0).toUInt64 * 0x10000 +
    (a.getD (o + 3) 0).toUInt64 * 0x1000000 + (a.getD (o + 4) 0).toUInt64 * 0x100000000 +
    (a.getD (o + 5) 0).toUInt64 * 0x10000000000 + (a.getD (o + 6) 0).toUInt64 * 0x1000000000000 +
    (a.getD (o + 7) 0).toUInt64 * 0x100000000000000

theorem u8_toNat_ofNat64 (x : UInt8) : UInt64.ofNat x.toNat = x.toUInt64 :=
  UInt64.toNat_inj.mp (by
    rw [UInt64.toNat_ofNat', UInt8.toNat_toUInt64]
    exact Nat.mod_eq_of_lt (by have := x.toNat_lt; omega))

theorem le8W_eq (a : Array UInt8) (o : ℕ) : (le8A a o).toUInt64 = le8W a o := by
  simp only [le8A, le8W, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.toUInt64_eq, UInt64.ofNat_add,
    UInt64.ofNat_mul, u8_toNat_ofNat64]
  simp only [Nat.reducePow, Nat.reduceMul]
  rw [show UInt64.ofNat 1 = 1 from rfl, UInt64.mul_one]
  rfl

/-- `pwOfA` at the base `pb`, in machine words. -/
def pwOfW (pb : ℕ) (a : Array UInt8) (y : ℕ) : Lvm.FK := Lvm.QSig.w64 (le8W a (8 * (y - pb)))

theorem pwOfW_eq (Ti : Ty.TInst6) (a : Array UInt8) : pwOfW (QD.pubBase Ti) a = pwOfA Ti a := by
  funext y
  simp only [pwOfW, pwOfA, le8W_eq]

/-- **`inst6` with the public words off an array** (the header's bytes built once per instance; VS1: in machine
words, the base `QD.pubBase` once per instance). -/
def inst6F (B : TyBase6) (h : staticOk6 B = true) (x : Hdr) : Ty.TyInst6 :=
  let pb := QD.pubBase B.Ti
  { inst6 B h x with pw := pwOfW pb (Lvm6.hdrBytes x).toArray }

theorem inst6F_eq (B : TyBase6) (h : staticOk6 B = true) : inst6F B h = inst6 B h := by
  funext x
  simp only [inst6F, pwOfW_eq, pwOfA_toArray]
  rfl

/-- **The deployed `S` branch**: `VSF6 base6 P17` reading the constants `guard6` (evaluated once per process) and
`shV6`, with the instance `inst6F` (`= inst6`), the decision `FB` (`= FH`; MUL2: the Keccak reductions, the
phases' claims and the opening on `m2B`) at PHIV8's Φ_Q evaluator `base6.P.eval8` (`= base6.P.eval` by
`PT.eval8_eq`, so `= F`) and the driver `VS6H` (`= VS6`). -/
def VSc6 : SProg := fun vk c π =>
  if h : guard6 = true then V.VS6H shV6 (V.FB (inst6F base6 h) base6.P.eval8 P17) vk c π else OProg.ret false

theorem VSc6_eq : VSc6 = VSF6 base6 P17 := by
  have e : VSc6 = fun vk c π =>
      if h : guard6 = true then V.VS6 shV6 (V.F (inst6 base6 h) base6.P P17) vk c π else OProg.ret false := by
    funext vk c π
    refine dite_congr rfl (fun h => ?_) (fun _ => rfl)
    have ev : base6.P.eval8 = base6.P.eval := funext (PT.eval8_eq _)
    rw [V.VS6H_eq, V.FB_eq, ev, V.FH_eq, inst6F_eq base6 h]
  rw [e]
  exact rfl

/-- **The deployed submission**: `submissionOf VSc6 (EX6D (accV VSc6) DD) (extX6 DD)` with the verifier run as
the byte-level twin `VwithT VSc6` (`Lvm6VWFast`) behind the kind test `isSB` (`VwithS`, VS1). -/
def submission6 : Submission :=
  { submissionOf VSc6 (EX6D (accV VSc6) DD) (extX6 DD) with V := VTw.VwithS VSc6 }

/-- The twin and the constants change nothing: `submission6` is the guarded submission at `base6`. -/
theorem submission6_eq :
    submission6 = submissionOf (VSF6 base6 P17) (EX6D (accV (VSF6 base6 P17)) DD) (extX6 DD) := by
  simp only [submission6, VTw.VwithS_eq, VTw.VwithT_eq, VSc6_eq]
  rfl

/-- **The certificate of the deployed submission** against `declared6`. -/
theorem certified6 : CertificateR declared6 submission6 := by
  rw [submission6_eq]
  exact certified6_base6

end Lvm6.Cert
