-- New for lvm2 roll 11 (M′, R11-IS): `σ′`'s regions lie in `C_main`'s stream block `S` (`2^19` words at
-- `CMain.sOff20`). The specification reads `σ′` from `S` as its `C_rec` column (`recOf20`) at `off mod 2^19`
-- (`TNat.inst`); V_S reads `C_main` at `off`. They agree when every `σ′` region lies in `S`, which `TNat.okB` does
-- not say (it asks `2^22 ≤ dst`, `dst + 2^log ≤ 7·2^20`). The lead puts `sigInSB NT20` into the guard (INT).
import LvmTypedVInst

/-!
# `σ′` in the stream block

* **`sigInSB N`**: every `σ′` region's target `[dst, dst + 2^log)` lies in `[sOff20, sOff20 + 2^19)` (a Bool check).
* **`SigInS N`**, **`sigInS_of`**: the Prop it decides.
* **`SBlk qm qr`**: `qr` is `qm`'s stream block (M′'s `C_rec` column, `recB20`).
* **`off_sigma`**: a word of a `σ′` region has `C_main` word `sOff20 + off mod 2^19` (`TNat.inst`'s `sigmaW`).
-/

set_option autoImplicit false

namespace Lvm.TypedV

/-- **`σ′`'s regions lie in `S`** (natively: one pass over the regions). -/
def sigInSB (N : TNat) : Bool :=
  N.regs.all fun g => g.src != .sigma ||
    (decide (CMain.sOff20 ≤ g.dst) && decide (g.dst + 2 ^ g.log ≤ CMain.sOff20 + 2 ^ 19))

/-- The Prop `sigInSB` decides. -/
def SigInS (N : TNat) : Prop :=
  ∀ g ∈ N.regs, g.src = .sigma → CMain.sOff20 ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ CMain.sOff20 + 2 ^ 19

/-- **`sigInSB` is sound.** -/
theorem sigInS_of {N : TNat} (h : sigInSB N = true) : SigInS N := by
  intro g hg hs
  have := List.all_eq_true.mp h g hg
  simp only [hs, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- `S` is `2^19`-aligned. -/
theorem sOff20_mod : CMain.sOff20 % 2 ^ 19 = 0 := by decide

/-- **A `σ′` word's `C_main` word is `S`'s word `off mod 2^19`** (the specification's `sigmaW`), and it lies in
`S`. -/
theorem off_sigma {N : TNat} (h : SigInS N) {y : ℕ} {g : NReg} (hr : N.regAt y = some g)
    (hs : g.src = .sigma) :
    N.off y = CMain.sOff20 + N.off y % 2 ^ 19 ∧ N.off y % 2 ^ 19 < 2 ^ 19 ∧
      CMain.sOff20 ≤ N.off y ∧ N.off y < CMain.sOff20 + 2 ^ 19 := by
  have hp := List.find?_some hr
  simp only [decide_eq_true_eq] at hp
  have hoff : N.off y = g.dst + (y - g.base) := by simp [TNat.off, hr]
  obtain ⟨h1, h2⟩ := h g (List.mem_of_find?_eq_some hr) hs
  have hlo : CMain.sOff20 ≤ N.off y := by omega
  have hhi : N.off y < CMain.sOff20 + 2 ^ 19 := by omega
  refine ⟨?_, Nat.mod_lt _ (Nat.two_pow_pos 19), hlo, hhi⟩
  have e : N.off y = 2 ^ 19 * 11 + (N.off y - CMain.sOff20) := by simp only [CMain.sOff20] at hlo ⊢; omega
  rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by simp only [CMain.sOff20] at hhi ⊢; omega)]
  simp only [CMain.sOff20] at hlo ⊢; omega

end Lvm.TypedV

namespace Lvm.NS

open LeanVM.Protocol

/-- **`qr` is `qm`'s stream block** (M′ `S2GM`: the specification's `C_rec` column is `C_main`'s block `S`,
`2^19` words at `CMain.sOff20`, `LvmCertM20.recB20`). -/
def SBlk (qm : Column CMain.nu20) (qr : Column 19) : Prop :=
  ∀ w < 2 ^ 19, qr.values.getD w 0 = qm.values.getD (CMain.sOff20 + w) 0

end Lvm.NS
