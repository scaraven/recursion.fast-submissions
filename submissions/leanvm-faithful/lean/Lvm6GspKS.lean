-- New for lvm6 (GSP, guard speed): KSA's `ksAliasB` and PHIV's `regsOkB` at run time.
-- `ksAliasB` looks each alias cell's word up through `Lay.wordK` (a scan of the blocks with `List.getD`, twice per
-- cell) and its constant through `Lay.cst?` (the constant regions' list lengths per cell); the twin reads NODE3's
-- owners list and the constants as arrays (`wordKO_eq`, `cstOfA_eq`). `regsOkB` walks every `com` word through
-- `regW6`'s region search. The `com` and `σ` conjuncts hold on every instance whose maps are `regW6`'s
-- (`MapsReg`, a field of `TyBase6`) and whose regions are disjoint (`regW6_affine`), so the twin checks `yDisjB`
-- in their place and the implication `regsOkB_of_regsOkBH` takes `MapsReg`. No statement changes.
import Lvm6NodeKS
import Lvm6NodeAsmChk
import Lvm6NodeMaps
import Lvm6VPhiReg

/-!
# `ksAliasBH` (`ksAliasB`) and `regsOkBH` (`regsOkB`)

* `ksCellP`, `ksAliasPP`: `ksCellB`, `ksAliasPB` with the constants and the words as arguments (`rfl` at
  `Lay.cst?`, `Lay.wordK`); **`ksAliasBH_eq : ksAliasBH Ti = (ksAliasChk Ti).b`**.
* `regAffB_regW6`: with disjoint regions, `regAffB` holds of `regW6` at every source.
  **`regsOkB_of_regsOkBH : MapsReg Ti → regsOkBH Ti = true → regsOkB Ti = true`**.
-/

set_option autoImplicit false

namespace Lvm6.Gsp

open Lvm.Typed Lvm6.Node.Dep Lvm6.Node.Asm
open Lvm6.Ty (TInst6)
open Lvm6.KSP (KSParams)
open Lvm6.Node.Mb (MbPar regW6)

/-! ## `ksAliasB` -/

/-- `ksCellB`, the constants `cs` and the words `wk` given (the word once). -/
def ksCellP (Ti : TInst6) (cs : ℕ → Option Lvm.FK) (wk : ℕ → ℕ) (n t : ℕ) : Bool :=
  let y := wk n
  (cs n).isNone && decide (Ti.src? y = some .ks) && decide (Ti.ksW y = t)

/-- `ksAliasPB`, the constants and the words given. -/
def ksAliasPP (P : KSParams) (Ti : TInst6) (cs : ℕ → Option Lvm.FK) (wk : ℕ → ℕ) : Bool :=
  P.fams.all fun f ↦ (List.range f.rows).all fun r ↦ (List.range f.w).all fun l ↦
    ksCellP Ti cs wk (f.c0 + f.w * r + l) (f.tgt r l)

theorem ksAliasPP_orig (P : KSParams) (Ti : TInst6) :
    ksAliasPP P Ti Ti.lay.cst? Ti.lay.wordK = ksAliasPB P Ti := rfl

/-- **`ksAliasB`, the owners list and the constants as arrays** (built once). -/
def ksAliasBH (Ti : TInst6) : Bool :=
  ksAliasPP ksP18 Ti (cstOfA (Ti.lay.cst.map fun r ↦ (r.1, r.2.toArray))) (wordKO (Lvm.Typed.K.fl_ownL Ti.lay .K) Ti.lay)

theorem ksAliasBH_eq (Ti : TInst6) : ksAliasBH Ti = (ksAliasChk Ti).b := by
  have e : (ksAliasChk Ti).b = ksAliasPB ksP18 Ti := by simp only [ksAliasChk, ksAliasB, Lvm6.Node.Chk.ofBool]
  rw [e, ← ksAliasPP_orig, ksAliasBH, cstOfA_eq, wordKO_eq]

/-! ## `regsOkB` -/

theorem regAffB_regW6 (P : MbPar) {Ti : TInst6} (hd : yDisjB Ti.lay.yregs = true) (s : YSrc) :
    Lvm6.V.regAffB Ti s (regW6 P Ti.lay s) = true := by
  simp only [Lvm6.V.regAffB, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq]
  intro reg hreg
  by_cases hs : reg.src = s
  · right
    intro i hi
    have h0 := regW6_affine P hd hreg hs (i := 0) (Nat.two_pow_pos _)
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [regW6_affine P hd hreg hs hi, h0]
  · exact Or.inl hs

/-- **`regsOkB` on an instance with `regW6`'s maps**: the regions disjoint, `ks` checked word by word. -/
def regsOkBH (Ti : TInst6) : Bool := yDisjB Ti.lay.yregs && Lvm6.V.regAffB Ti .ks Ti.ksW

theorem regsOkB_of_regsOkBH {Ti : TInst6} (hM : MapsReg Ti) (h : regsOkBH Ti = true) :
    Lvm6.V.regsOkB Ti = true := by
  simp only [regsOkBH, Bool.and_eq_true] at h
  obtain ⟨hd, hk⟩ := h
  rw [Lvm6.V.regsOkB, hM.1, hM.2.2, regAffB_regW6 _ hd, regAffB_regW6 _ hd, hk]
  rfl

end Lvm6.Gsp
