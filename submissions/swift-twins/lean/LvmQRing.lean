-- New for lvm (WP-11b-QA2, helper H1). Searched for reuse: FR `FRRingSwitch.lean` (Φ as a staged
-- Frobenius map on a generic `CommRing`, weight lemmas), leanerVM
-- `Protocol/ToArkLib/Flock/RingSwitch.lean`, our `LvmRingFidelity` (`ringWeight_fold`,
-- `phiMap_eq_sum` on the protocol's `E`). None has LoopIR gadgets; the weight fold of
-- `LvmQRingWeight` is adapted from `LvmRingFidelity.ringWeight_fold` (restated on `Lvm.FE`).
import LvmQBuildLemmas
import LvmDecideKeccak
import LvmSelfEval

-- (GOLF2: 23 declarations that `certified` does not use moved verbatim to `LvmFinPosOff`, outside its import closure.)

/-!
# QA2 ring switching, part 1: one-row loops and the Frobenius coefficients

`F`'s ring switching (`LvmDecideKeccak`: `ringCoefficients`, `phiMap`, `ringWeight`, `ringSwitch`)
as LoopIR gadgets written with the builder (`LvmQBuild`). This module:

* `madL`, `linL`, `loadL`: a loop of one `E` row with affine operands (`a₀·a₁ + a₂`,
  `a₀ + k·a₁ + k'`, `loadE`); `madL_spec` etc.: the result at flat index `jf` is cell `p.e + jf`.
* `frobTab b f z`: the Frobenius table `f^(2^m)`, `m ≤ 2^b` (a copy of `f`, then `2^b` squarings);
  `2^b + 1` rows.
* `coeffs ch z`: the 64 coefficients `c_k` (`ringCoefficients`) from the six challenges in the
  `E` cells `ch + i`: tables for the shifts `32, …, 2` (the shift-1 table is the challenge cell),
  `c₀ = 1`, then per level `b`: `c_{2^b + m} = c_m · f_{5-b}^(2^m)` (`m < 2^b`). 131 rows (tables
  5 copies + 62 squarings, `c₀`, 63 level rows); the coefficients are the 64 cells before the
  pointer after the gadget (`coeffs_out`, `coeffs_adv`).
* `coeffs_eq`: **the cells are `F`'s `ringCoefficients ch`** (via the closed form `coefV`,
  `ringCoefficients_getD`, and its level recursion `coefV_level`).
-/

set_option autoImplicit false

namespace Lvm.Loop.QRing

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## One-row loops -/

/-- An `E` operand `base + Σ_d strides[d]·j_d`. -/
abbrev eA (base : Nat) (s : List Nat) : Addr := ⟨.E, base, s⟩

/-- A loop of one `E` row `a₀·a₁ + a₂`. -/
def madL (dims : List Nat) (a₀ a₁ a₂ : Addr) : BM LoopOut :=
  loop dims [⟨.muladd, .E, [.abs a₀, .abs a₁, .abs a₂]⟩]

/-- A loop of one `E` row `a₀ + k·a₁ + k'`. -/
def linL (dims : List Nat) (k k' : FK) (a₀ a₁ : Addr) : BM LoopOut :=
  loop dims [⟨.lin k k', .E, [.abs a₀, .abs a₁]⟩]

/-- A loop of one `loadE` row (`E` from three `K` operands). -/
def loadL (dims : List Nat) (a₀ a₁ a₂ : Addr) : BM LoopOut :=
  loop dims [⟨.loadE, .E, [.abs a₀, .abs a₁, .abs a₂]⟩]

variable {c : Ctx} {M : Mem}

theorem madL_adv (dims : List Nat) (a₀ a₁ a₂ : Addr) (p : Ptr) :
    p.adv (madL dims a₀ a₁ a₂ p).2 = ⟨p.k, p.e + 2 ^ dims.sum⟩ := by
  simp [madL, loop, Ptr.adv, segsW, Seg.w, mkLoop, Block.tw, Block.size, Block.lsize, Row.w,
    Row.writes]

theorem linL_adv (dims : List Nat) (k k' : FK) (a₀ a₁ : Addr) (p : Ptr) :
    p.adv (linL dims k k' a₀ a₁ p).2 = ⟨p.k, p.e + 2 ^ dims.sum⟩ := by
  simp [linL, loop, Ptr.adv, segsW, Seg.w, mkLoop, Block.tw, Block.size, Block.lsize, Row.w,
    Row.writes]

theorem linL_adv' (dims : List Nat) (n : Nat) (hn : 2 ^ dims.sum = n) (k k' : FK) (a₀ a₁ : Addr)
    (p : Ptr) : p.adv (linL dims k k' a₀ a₁ p).2 = ⟨p.k, p.e + n⟩ := by rw [linL_adv, hn]

@[simp] theorem madL_p (dims : List Nat) (a₀ a₁ a₂ : Addr) (p : Ptr) :
    (madL dims a₀ a₁ a₂ p).1.p = p := rfl
@[simp] theorem linL_p (dims : List Nat) (k k' : FK) (a₀ a₁ : Addr) (p : Ptr) :
    (linL dims k k' a₀ a₁ p).1.p = p := rfl
@[simp] theorem loadL_p (dims : List Nat) (a₀ a₁ a₂ : Addr) (p : Ptr) :
    (loadL dims a₀ a₁ a₂ p).1.p = p := rfl

-- adapted from LvmQWhirBase.lt_size_la
theorem lt_two_dims {l a k q : Nat} (hk : k < 2 ^ l) (hq : q < 2 ^ a) :
    k + 2 ^ l * q < 2 ^ (l + a) := by
  rw [pow_add]
  calc k + 2 ^ l * q < 2 ^ l * (q + 1) := by rw [Nat.mul_succ]; (clear * - hk; omega)
    _ ≤ 2 ^ l * 2 ^ a := Nat.mul_le_mul_left _ hq

theorem madL_spec {dims : List Nat} {a₀ a₁ a₂ : Addr} {p : Ptr}
    (h : SegsHold c M p (madL dims a₀ a₁ a₂ p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    M.e (p.e + jf) = M.rd a₀.ty (a₀.at (unflat dims jf)) * M.rd a₁.ty (a₁.at (unflat dims jf)) +
      M.rd a₂.ty (a₂.at (unflat dims jf)) := by
  have := loop_rel (t := 0) h hjf (by simp)
  rw [loop_apply] at this
  simpa [LRel, LoopOut.cell, LoopOut.arg, lrank, ltw, LRow.w, Row.w, Row.writes, Opd.val_abs,
    Cell.val, Mem.rd, Ptr.at] using this

theorem linL_spec {dims : List Nat} {k k' : FK} {a₀ a₁ : Addr} {p : Ptr}
    (h : SegsHold c M p (linL dims k k' a₀ a₁ p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    M.e (p.e + jf) = M.rd a₀.ty (a₀.at (unflat dims jf)) +
      FE.ofK k * M.rd a₁.ty (a₁.at (unflat dims jf)) + FE.ofK k' := by
  have := loop_rel (t := 0) h hjf (by simp)
  rw [loop_apply] at this
  simpa [LRel, LoopOut.cell, LoopOut.arg, lrank, ltw, LRow.w, Row.w, Row.writes, Opd.val_abs,
    Cell.val, Mem.rd, Ptr.at] using this

/-- The `E` copy row: result at `p.e`, value of `a`. -/
theorem copyE_spec {a : Nat} {p : Ptr} (h : SegsHold c M p (copy (ec a) p).2) :
    (copy (ec a) p).1 = ec p.e ∧ M.e p.e = M.e a := by
  have := lin_spec h
  refine ⟨rfl, ?_⟩
  simpa [copy, lin, rowRes, Cell.val, Mem.rd, Ptr.at, ofK_zero] using this

theorem copyE_adv (a : Nat) (p : Ptr) : p.adv (copy (ec a) p).2 = ⟨p.k, p.e + 1⟩ := by
  simp [copy, lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

/-- Sequencing a gadget with known output `x` and pointer after `p'`. -/
theorem hold_bind_eq {α β : Type} {m : BM α} {f : α → BM β} {p p' : Ptr} {x : α}
    (hx : (m p).1 = x) (hp : p.adv (m p).2 = p') :
    SegsHold c M p ((m >>= f) p).2 ↔ SegsHold c M p (m p).2 ∧ SegsHold c M p' (f x p').2 := by
  rw [hold_bind, hx, hp]

theorem bind_fst_eq {α β : Type} {m : BM α} {f : α → BM β} {p p' : Ptr} {x : α}
    (hx : (m p).1 = x) (hp : p.adv (m p).2 = p') : ((m >>= f) p).1 = (f x p').1 := by
  rw [bind_apply, hx, hp]

theorem bind_adv_eq {α β : Type} {m : BM α} {f : α → BM β} {p p' : Ptr} {x : α}
    (hx : (m p).1 = x) (hp : p.adv (m p).2 = p') :
    p.adv ((m >>= f) p).2 = p'.adv (f x p').2 := by
  rw [bind_apply, Ptr.adv_append, hp, hx]

theorem getPtr_out (p : Ptr) : (getPtr p).1 = p := rfl
theorem getPtr_adv (p : Ptr) : p.adv (getPtr p).2 = p := Ptr.adv_nil p

theorem copy_out (a : Cell) (p : Ptr) : (copy a p).1 = ⟨a.ty, p.at a.ty⟩ := rfl

theorem constE_adv (k' : FK) (x : Cell) (p : Ptr) : p.adv (const .E k' x p).2 = ⟨p.k, p.e + 1⟩ := by
  simp [const, lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

/-! ## Frobenius tables -/

/-- `f^(2^m)` for `m ≤ 2^b` at the returned cell `+ m`: a copy of `f`, then `2^b` squarings. -/
def frobTab (b f z : Nat) : BM Nat := do
  let q ← copy (ec f)
  let _ ← madL [b] (eA q.n [1]) (eA q.n [1]) (eA z [])
  pure q.n

/-! ## The coefficients -/

/-- One level of the coefficient table: `c_{2^b + m} = c_m · F[m] + z`. -/
def cLevels (cb z : Nat) : Nat → List Nat → BM Unit
  | _, [] => pure ()
  | b, fb :: fbs => do
    let _ ← madL [b] (eA cb [1]) (eA fb [1]) (eA z [])
    cLevels cb z (b + 1) fbs

/-- The Frobenius tables a run of levels reads: level `b`'s table holds `f_{5-b}^(2^m)`. -/
def TabsOk (M : Mem) (fc : Nat → FE) : Nat → List Nat → Prop
  | _, [] => True
  | b, fb :: fbs => (∀ m < 2 ^ b, M.e (fb + m) = fc (5 - b) ^ 2 ^ m) ∧ TabsOk M fc (b + 1) fbs

/-- **The coefficients** from the challenges in `E` cells `ch + i` (`z` an `E` zero cell): the
returned cell `+ k`, `k < 64`, holds `c_k`; they are the 64 cells before the pointer after it. -/
def coeffs (ch z : Nat) : BM Nat := do
  let t5 ← frobTab 5 ch z
  let t4 ← frobTab 4 (ch + 1) z
  let t3 ← frobTab 3 (ch + 2) z
  let t2 ← frobTab 2 (ch + 3) z
  let t1 ← frobTab 1 (ch + 4) z
  let c0 ← const .E 1 (ec z)
  cLevels c0.n z 0 [ch + 5, t1, t2, t3, t4, t5]
  pure c0.n

end Lvm.Loop.QRing

namespace Lvm.Loop.QRing

open Lvm Lvm.Loop Lvm.Loop.Build

variable {c : Ctx} {M : Mem}

end Lvm.Loop.QRing
