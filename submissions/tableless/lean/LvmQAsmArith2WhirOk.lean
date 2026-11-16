-- Moved out of `LvmQAsmArith2WhirLS` (`okb`) and `LvmQAsmArith2WhirGS` (`adv_e_le`) (lvm2 roll 8, wave L, L-W; a pure
-- move): the two pointer/`Ok` lemmas that the typed HAR (`LvmQTypedHar*`) reads through the B program's definitions'
-- path, so that path need not import `LvmQAsmArith2WhirLS` (a shorter build critical path).
import LvmQAsmArith2WhirG

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build DM

variable {c : Ctx} {M : Mem}

theorem adv_e_le (p : Ptr) (δ : List Seg) : p.e ≤ (p.adv δ).e := Nat.le_add_right _ _

theorem okb {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr} (h : Lvm.QSig.Ok c M (m >>= f) p) :
    Lvm.QSig.Ok c M m p ∧ Lvm.QSig.Ok c M (f (m p).1) (p.adv (m p).2) := by
  obtain ⟨h1, h2⟩ := h
  rw [hold_bind] at h1; rw [assert_bind] at h2
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

end Lvm.Har
