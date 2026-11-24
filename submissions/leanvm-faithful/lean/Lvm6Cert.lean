-- New for lvm6 (WP C6 of CERT, links 1, 2, 13, 15): the final assembly. The certificate with the `S` branch
-- behind the guard, for either value of the guard, and the deployed submission over top-level constants.
import Lvm6CertExt
import Lvm6CertMA
import Lvm6VGuard6
import Lvm6WOnly
import Lvm6VS1F
import Lvm6VM2F
import Lvm6VS1W
import Lvm6VS1Drv
import Lvm6VPhiE8

/-!
# The certificate of the lvm6 submission (WP C6)

The submission is `submissionOf (VSF6 B P18) (EX6D (accV (VSF6 B P18)) D18) (extX6 D18)`: the `S` branch is the
fast verifier behind the guard `staticOk6 B`, the extractor specification is C4's domain split `EX6D` and the
program is `extX6 D18`.

* **`certified_ofS`** (link 1, season 1's form): the certificate against `declared6` from `SSound` (any scheme
  that the branch refines), the query bound, `computes`, `size` and the `W` branch.
* **`certified_off`** (link 2, guard off): `VSoff` with any extractor that computes, fits and decodes `W` proofs
  (`sSound_off`); **`certified_offD`** at `EX6D` and `extX6 D18`.
* **`certified_on`** (guard on): C4's `certified_ofD` with C3's `open6X18D_Φ6`, C5's `Xe6`, C3's `queries_VSasm`
  and `refines6_asm`, at `V_S = VSasm (Φ6 B h)`, from `node6V` there.
* **`certified6_guard`**: for any base `B` whose phases satisfy `node6V` when the guard holds, the certificate of
  the guarded submission. Off: `VSF6 B P18 = VSoff`. On: `VSF6_eqP18` (C1), the guard's branch of `VSspec6`, then
  `VSasm_Φ6` (C3). **`certified6_tiOf6`**: every `tiOf6 P` (`node6V_Φ6`); **`certified6_base6`**: the deployed
  `base6` (`base6_eq`).
* **Link 15, the compiled verifier**: `shV6 = toV P18` and the guard `guard6 = staticOk6 base6` (V1c's
  `Lvm6VGuard6`; the base `B6` of the plan is `base6`) are top-level constants, so the badge evaluates them once
  per process when it loads, never inside a timed check. `VSc6` reads them, with the instance
  `inst6F` (VFIX: `inst6` with the public words read off an array; VS1: in machine words; `inst6F_eq`) and VS1's
  decision `FH` (MUL2: as `FB`, the Keccak reductions, the phases' claims and the opening on `m2B`, `FB_eq`) at
  PHIV8's Φ_Q evaluator `base6.P.eval8` (`PT.eval8_eq`, `FH_eq`), driven by VS1's `VS6H` (`VS6H_eq`);
  `VSc6_eq : VSc6 = VSF6 base6 P18`.
  **`submission6`** runs the verifier as the byte-level twin `VwithT VSc6` behind VS1's kind test (`VwithS`);
  `submission6_eq` rewrites by `VwithS_eq` and `VwithT_eq`. **`certified6 : CertificateR declared6 submission6`**.
-/

set_option autoImplicit false

namespace Lvm6.Cert

open RecursionFast Lvm.T Lvm.X LeanVM.Parameters
open RecursionFast.WitnessSending (decode)
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm6.V (TyBase6 staticOk6 inst6 VSF6 VSspec6 Φ6 PT base6 guard6)
open Lvm6.X (EX6D extX6 fillIR18 descX6 Lv18 F18 finX18)
open scoped NNReal

/-- The extractor's descent at `P18`: the fill, then the levels and the final opening. -/
abbrev D18 : XIR := .seq fillIR18 (descX6 (Lv18 F18) finX18)

/-! ## Link 1, season 1's form: from `SSound` -/

/-- **The certificate against `declared6` from `SSound`**: the `S` branch's knowledge soundness through a scheme it
refines (season 1's `SSound`), its query bound, the program's `Computes` within `fuel6` and size, and the
extractor's `W` branch. -/
theorem certified_ofS {VS : SProg} {EX : Digest → Proof → Log → Option Wit} {extX : XProg}
    (hq : ∀ H vk c π, isS π = true → ((VS vk c π).queries H).length ≤ qVlvm)
    (hc : Computes extX EX fuel6) (hsz : extX.body.size ≤ progCap)
    (hEW : ∀ c π L, isS π = false → EX c π L = decode π) (hS : ∀ vk, SSound VS EX vk) :
    CertificateR declared6 (submissionOf VS EX extX) := by
  refine ⟨⟨fun vk => ks_subWith VS EX extX hq hEW vk (hS vk), fun vk => ?_, hc, ?_⟩, ?_⟩
  · rw [submissionOf_δ]; exact complete VS _ rfl rfl rfl vk
  · refine ⟨by rw [submissionOf_ε]; rfl, by rw [submissionOf_δ]; exact zero_le,
      show qVlvm ≤ 2 ^ 16 by decide, fun t => ?_, hsz⟩
    simp only [submissionOf, fuel6, extractorBudget]; omega
  · refine ⟨?_, by simp [submissionOf, declared6], le_rfl, fun t => ⟨le_of_eq ?_, ?_⟩⟩
    · simp only [submissionOf, declared6]; push_cast; norm_num
    · simp [submissionOf, declared6, fuel6]
    · simp only [declared6, extractorBudget]; omega

/-! ## Link 2: the guard off -/

/-- **The certificate with the `S` branch off**, for every extractor that the program computes within `fuel6`, that
fits `progCap` and that decodes `W` proofs (`sSound_off`). -/
theorem certified_off {EX : Digest → Proof → Log → Option Wit} {extX : XProg}
    (hc : Computes extX EX fuel6) (hsz : extX.body.size ≤ progCap)
    (hEW : ∀ c π L, isS π = false → EX c π L = decode π) :
    CertificateR declared6 (submissionOf W.VSoff EX extX) :=
  certified_ofS (fun _ _ _ _ _ => by simp [W.VSoff, OProg.queries]) hc hsz hEW
    (fun vk => W.sSound_off EX vk)

/-- `certified_off` at C4's extractor `EX6D A D18` and the program `extX6 D18`, for every acceptance `A`. -/
theorem certified_offD (A : Digest → Digest → Signed → Bool) :
    CertificateR declared6 (submissionOf W.VSoff (EX6D A D18) (extX6 D18)) :=
  certified_off (X.computes6D A _ X.descOk6_F18) (X.size_extX6 (X.sizeIR_F18 F18)) (X.wBranch6D A _)

/-! ## Link 2: the guard on -/

/-- **The certificate at C3's phases** `Φ6 B h`, from the node theorem there (`Xe6`, C5). -/
theorem certified_on (B : TyBase6) (h : staticOk6 B = true)
    (hN : Stmt.node6V (VSasm (Φ6 B h)) (Node.Asm.rest6 B h) (Node.childOf6 Node.Asm.trOfS Node.Asm.σOfS)
      Node.Asm.σlOfS) :
    CertificateR declared6
      (submissionOf (VSasm (Φ6 B h) P18) (EX6D (accV (VSasm (Φ6 B h) P18)) D18) (extX6 D18)) :=
  certified_ofD (VS := VSasm (Φ6 B h))
    { X.open6X18D_Φ6 (VS := VSasm (Φ6 B h)) B h (Xe6 B h hN) (Xe6_ext B h hN) with
      queries := V.queries_VSasm (Φ6 B h)
      refines := refines6_asm (Φ6 B h) P18 }

/-- **With the guard on, the guarded fast `V_S` is `VSasm (Φ6 B h)` at `P18`** (`VSF6_eqP18`, C1; `VSasm_Φ6`,
C3). -/
theorem VSF6_on {B : TyBase6} (h : staticOk6 B = true) : VSF6 B P18 = VSasm (Φ6 B h) P18 := by
  rw [V.VSF6_eqP18, ← V.VSasm_Φ6 B h]
  funext vk c π
  simp [VSspec6, h]

/-- **With the guard off, the guarded fast `V_S` is `VSoff`.** -/
theorem VSF6_off {B : TyBase6} {sh : Shape} (h : ¬ staticOk6 B = true) : VSF6 B sh = W.VSoff := by
  funext vk c π
  simp [VSF6, h, W.VSoff]

/-- **The certificate of the guarded submission** (link 2), for either value of the guard, for every base `B`
whose phases satisfy the node theorem when the guard holds. -/
theorem certified6_guard (B : TyBase6)
    (hN : ∀ h : staticOk6 B = true, Stmt.node6V (VSasm (Φ6 B h)) (Node.Asm.rest6 B h)
      (Node.childOf6 Node.Asm.trOfS Node.Asm.σOfS) Node.Asm.σlOfS) :
    CertificateR declared6
      (submissionOf (VSF6 B P18) (EX6D (accV (VSF6 B P18)) D18) (extX6 D18)) := by
  by_cases h : staticOk6 B = true
  · rw [VSF6_on h]
    exact certified_on B h (hN h)
  · rw [VSF6_off h]
    exact certified_offD _

/-- `certified6_guard` at the base `tiOf6 P` of every class table `P` (`node6V_Φ6`). -/
theorem certified6_tiOf6 (P : PT) :
    CertificateR declared6 (submissionOf (VSF6 (Node.Ti.tiOf6 P) P18)
      (EX6D (accV (VSF6 (Node.Ti.tiOf6 P) P18)) D18) (extX6 D18)) :=
  certified6_guard _ (V.node6V_Φ6 P)

/-- `certified6_guard` at every base equal to some `tiOf6 P`. -/
theorem certified6_of_eq {B : TyBase6} {P : PT} (e : B = Node.Ti.tiOf6 P) :
    CertificateR declared6 (submissionOf (VSF6 B P18) (EX6D (accV (VSF6 B P18)) D18) (extX6 D18)) := by
  subst e
  exact certified6_tiOf6 P

/-- **The certificate at the deployed base `base6`** (`base6_eq`). -/
theorem certified6_base6 :
    CertificateR declared6 (submissionOf (VSF6 base6 P18) (EX6D (accV (VSF6 base6 P18)) D18) (extX6 D18)) :=
  certified6_of_eq V.base6_eq

/-! ## Link 15: the compiled verifier over top-level constants -/

/-- **The verifier's shape at `P18`**, a top-level constant. -/
def shV6 : V.VShape := toV P18

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

/-- **The deployed `S` branch**: `VSF6 base6 P18` reading the constants `guard6` (evaluated once per process) and
`shV6`, with the instance `inst6F` (`= inst6`), the decision `FB` (`= FH`; MUL2: the Keccak reductions, the
phases' claims and the opening on `m2B`) at PHIV8's Φ_Q evaluator `base6.P.eval8` (`= base6.P.eval` by
`PT.eval8_eq`, so `= F`) and the driver `VS6H` (`= VS6`). -/
def VSc6 : SProg := fun vk c π =>
  if h : guard6 = true then V.VS6H shV6 (V.FB (inst6F base6 h) base6.P.eval8 P18) vk c π else OProg.ret false

theorem VSc6_eq : VSc6 = VSF6 base6 P18 := by
  have e : VSc6 = fun vk c π =>
      if h : guard6 = true then V.VS6 shV6 (V.F (inst6 base6 h) base6.P P18) vk c π else OProg.ret false := by
    funext vk c π
    refine dite_congr rfl (fun h => ?_) (fun _ => rfl)
    have ev : base6.P.eval8 = base6.P.eval := funext (PT.eval8_eq _)
    rw [V.VS6H_eq, V.FB_eq, ev, V.FH_eq, inst6F_eq base6 h]
  rw [e]
  exact rfl

/-- **The deployed submission**: `submissionOf VSc6 (EX6D (accV VSc6) D18) (extX6 D18)` with the verifier run as
the byte-level twin `VwithT VSc6` (`Lvm6VWFast`) behind the kind test `isSB` (`VwithS`, VS1). -/
def submission6 : Submission :=
  { submissionOf VSc6 (EX6D (accV VSc6) D18) (extX6 D18) with V := VTw.VwithS VSc6 }

/-- The twin and the constants change nothing: `submission6` is the guarded submission at `base6`. -/
theorem submission6_eq :
    submission6 = submissionOf (VSF6 base6 P18) (EX6D (accV (VSF6 base6 P18)) D18) (extX6 D18) := by
  simp only [submission6, VTw.VwithS_eq, VTw.VwithT_eq, VSc6_eq]
  rfl

/-- **The certificate of the deployed submission** against `declared6`. -/
theorem certified6 : CertificateR declared6 submission6 := by
  rw [submission6_eq]
  exact certified6_base6

end Lvm6.Cert
