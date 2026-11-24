-- New for lvm6 (WP NODE3). The wiring bridge (NODE §7 (ii)): the typed relation `TGoodE` of an instance whose
-- program is a gadget's (`toProgramF`) gives that gadget's segments and assertions at the program's first
-- pointer, so every `HsA` conclusion of the gadget holds on the memory read off the candidate's words.
import Lvm6NodeQ
import Lvm6TySpecP
import LvmVFastQ

/-!
# `TGoodE ⟹ SegsHold ∧ SegsAssert` (WP NODE3, item 5)

* **`segs_of_tgoodE`**: for `Ti.Q = toProgramF nK nE m`, with the program and twin checks (`wf`, `twinsOk`), no
  `E3` row (`NoE3`), the instance check `Ti.Ok` and the mini-bus obligation `ReaddOk`, the first conjunct of
  `TGoodE` (the relation at `E2`) gives `SegsHold` and `SegsAssert` of `m`'s segments at `⟨nK, nE⟩` on
  `memOf Ti.lay (Ti.zOf …)`. Season 1's `holds_of_wiringT` (through `wiringRelE_iff`), then
  `toProgram_holds`/`toProgram_asserts`.
* **`hsA_of_tgoodE`**: an `HsA` fact of `m` (in the program's context) holds of `m`'s output there.
* **`hsA_first_of_tgoodE`**: for a program that runs `m` first (`m >>= f`), an `HsA` fact of `m` holds of some
  output; with `node6E_har` this gives the tree, sponge, link and typed conclusions on the deployed program.

The static facts (`wf`, `twinsOk`, `NoE3`, `Ti.Ok`) are the guard's (`staticOk6`); `ReaddOk` is the mini-bus's.
-/

set_option autoImplicit false

namespace Lvm6.Node

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Typed Lvm.Har Lvm.E2V Lvm.Q2 LeanVM.Protocol
open Lvm6.Ty (TInst6 TGoodE WiringRelE NoE3 wiringRelE_iff)
open Lvm6.QK
open Lvm6.QD

/-- The memory a candidate pair's words define (`memOf` of `zOf`). -/
noncomputable def memTi (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → FK) (p : Column L.nuMain × Column L.nuRec) : Mem :=
  memOf Ti.lay (Ti.zOf L pw p.1 p.2)

/-- **The wiring bridge**: the typed relation gives the gadget's segments and assertions. -/
theorem segs_of_tgoodE {α : Type} (m : BM α) (nK nE : ℕ) (Ti : TInst6) (L : Lvm.M3.Lay)
    (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ) (pw : ℕ → FK) (p : Column L.nuMain × Column L.nuRec)
    (hQ : Ti.Q = Lvm.VF.toProgramF nK nE m) (hwf : Ti.Q.wf = true) (htw : Ti.Q.twinsOk = true)
    (hE3 : NoE3 Ti.Q Ti.lay) (hok : Ti.Ok) (hrd : ReaddOk Ti.Q (memTi Ti L pw p))
    (hg : TGoodE Ti L hτ pw p) :
    SegsHold (ctxOf Ti.Q) (memTi Ti L pw p) ⟨nK, nE⟩ (m ⟨nK, nE⟩).2 ∧
      SegsAssert (memTi Ti L pw p) ⟨nK, nE⟩ (m ⟨nK, nE⟩).2 := by
  have hone : Ti.zOf L pw p.1 p.2 Ti.lay.one = 1 := by
    unfold TInst6.zOf
    rw [hok.2]
  have hT := (wiringRelE_iff hok.1 hE3).mp hg.1
  obtain ⟨hH, hA⟩ := holds_of_wiringT Ti.Q Ti.lay _ hwf htw hok.1 hone hT hrd
  have hQ' : Ti.Q = toProgram nK nE m := by rw [hQ, Lvm.VF.toProgramF_eq]
  rw [hQ'] at hH hA ⊢
  exact ⟨(toProgram_holds nK nE m _).mp hH, (toProgram_asserts nK nE m _).mp hA⟩

/-- **An `HsA` fact of the program's gadget holds** on a good pair's memory. -/
theorem hsA_of_tgoodE {α : Type} (m : BM α) (nK nE : ℕ) (Ti : TInst6) (L : Lvm.M3.Lay)
    (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ) (pw : ℕ → FK) (p : Column L.nuMain × Column L.nuRec)
    (hQ : Ti.Q = Lvm.VF.toProgramF nK nE m) (hwf : Ti.Q.wf = true) (htw : Ti.Q.twinsOk = true)
    (hE3 : NoE3 Ti.Q Ti.lay) (hok : Ti.Ok) (hrd : ReaddOk Ti.Q (memTi Ti L pw p))
    (hg : TGoodE Ti L hτ pw p) {P : α → Prop} (h : HsA (ctxOf Ti.Q) (memTi Ti L pw p) m P) :
    P (m ⟨nK, nE⟩).1 := by
  obtain ⟨hH, hA⟩ := segs_of_tgoodE m nK nE Ti L hτ pw p hQ hwf htw hE3 hok hrd hg
  exact h _ hH hA

/-- An `HsA` fact of the first part of a composed gadget. -/
theorem hsA_bind_fst {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} {P : α → Prop}
    (h : HsA c M m P) : HsA c M (m >>= f) fun _ ↦ ∃ a, P a := by
  refine hsA_bind h fun a ha ↦ ?_
  intro _ _ _
  exact ⟨a, ha⟩

/-- **The first part of the program**: an `HsA` fact of `m` holds of some output when `Ti.Q` runs `m >>= f`. -/
theorem hsA_first_of_tgoodE {α β : Type} (m : BM α) (f : α → BM β) (nK nE : ℕ) (Ti : TInst6) (L : Lvm.M3.Lay)
    (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ) (pw : ℕ → FK) (p : Column L.nuMain × Column L.nuRec)
    (hQ : Ti.Q = Lvm.VF.toProgramF nK nE (m >>= f)) (hwf : Ti.Q.wf = true) (htw : Ti.Q.twinsOk = true)
    (hE3 : NoE3 Ti.Q Ti.lay) (hok : Ti.Ok) (hrd : ReaddOk Ti.Q (memTi Ti L pw p))
    (hg : TGoodE Ti L hτ pw p) {P : α → Prop} (h : HsA (ctxOf Ti.Q) (memTi Ti L pw p) m P) : ∃ a, P a :=
  hsA_of_tgoodE (m >>= f) nK nE Ti L hτ pw p hQ hwf htw hE3 hok hrd hg (P := fun _ ↦ ∃ a, P a) (hsA_bind_fst h)

end Lvm6.Node
