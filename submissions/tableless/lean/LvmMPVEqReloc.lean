-- New for lvm2 roll 11 (M′, R11-IR): the relocation of a `C_rec` stack claim onto `C_main`'s stream block `S`
-- (`relocS`, the language side of `LvmCertM20.relocB20`) and the closed forms that tie V_S's `C_main` claims on `S`
-- (the relayout's point claim, the `KS` link's `M`, `σ′`'s region claim) to the relocated spec claims.
import LvmVEqMid
import LvmEqLemmas
import LvmLayoutArith
import LvmRingFidelity

-- (GOLF2: 3 declarations that `certified` does not use moved verbatim to `LvmVEqTopOff`, outside its import closure.)

/-!
# Claims on the stream block `S`

* **`relocS c`**: the `C_rec` stack claim `c` as the block claim `⟨19, sOff20⟩` on `C_main` (its weight on the block's
  own 19 variables, the selector of `S` above them).
* `eqAbove_eqAt`: a placement's selector is `eqAt` of the coordinates above it; `eqAt_split_hi`: an index splits
  at any coordinate; **`eqAt_reloc`**: `eq(X, m)` for a word `m` of `S` is `S`'s selector times `eq(X_{<19}, m)`.
* **`eqAbove_reloc`**: a block `⟨k, b⟩` of `C_main` inside `S` is `S`'s selector times the block `⟨k, o⟩` of the
  19-variable cube (given the three index identities `b = S + o` implies, `reloc_idx`).
* **`relocS_point`** (`⟨19, S⟩`'s point claim), **`relocS_sum`** (a sum claim on `C_main` whose parts lie in `S`):
  V_S's claims on `S` are the relocated `C_rec` claims, as functions.
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (eqAt eqAt_cons eqAt_nil eqAt_mod eqAt_append)

/-- **A `C_rec` stack claim relocated onto `C_main`'s stream block `S`** (M′; `LvmCertM20.relocB20`). -/
def relocS (c : VStackClaim) : VStackClaim := (⟨⟨19, CMain.sOff20⟩, c.1, c.2⟩ : BClaim).onStack

/-- A placement's selector is the equality weight of the coordinates above its window. -/
theorem eqAbove_eqAt (p : VPlacement) (y : List E) :
    p.eqAbove y = eqAt (y.drop p.variableCount) (p.index >>> p.variableCount) := by
  unfold LeanVM.Protocol.Verifier.Placement.eqAbove
  rw [LeanVM.Protocol.EndToEnd.Front.selectorPoint_eq_boolPoint, LeanVM.Protocol.Whir.Complete.eqEval_comm,
    ← List.length_drop, LeanVM.Protocol.EndToEnd.Front.eqEval_boolPoint_eqAt]

/-- An index splits at coordinate `l` (any length). -/
theorem eqAt_split_hi (X : List E) (m l : ℕ) : eqAt X m = eqAt (X.take l) m * eqAt (X.drop l) (m >>> l) := by
  conv_lhs => rw [← List.take_append_drop l X]
  rw [eqAt_append]
  rcases le_or_gt l X.length with hl | hl
  · rw [List.length_take_of_le hl, Nat.shiftRight_eq_div_pow]
  · rw [List.drop_of_length_le hl.le, eqAt_nil, eqAt_nil]

/-- **A `C_rec` stack claim relocated onto `C_main`'s stream block at `S`** (`relocS`'s, at any stream block). -/
def relocSAt (S : ℕ) (c : VStackClaim) : VStackClaim := (⟨⟨19, S⟩, c.1, c.2⟩ : BClaim).onStack

theorem relocS_eq_At : relocS = relocSAt CMain.sOff20 := rfl

/-- **A word of the stream block at `S`**: `eq(X, m) = sel_S(X) · eq(X_{<19}, m)` when `m` and `S` agree above
bit 19. -/
theorem eqAt_relocAt (S : ℕ) (X : List E) (m : ℕ) (h : m >>> 19 = S >>> 19) :
    eqAt X m = (⟨19, S⟩ : VPlacement).eqAbove X * eqAt (X.take 19) m := by
  rw [eqAbove_eqAt, eqAt_split_hi X m 19, h]
  exact mul_comm _ _

/-- **A word of `S`** (`eqAt_relocAt` at M′'s `S`). -/
theorem eqAt_reloc (X : List E) (m : ℕ) (h : m >>> 19 = CMain.sOff20 >>> 19) :
    eqAt X m = (⟨19, CMain.sOff20⟩ : VPlacement).eqAbove X * eqAt (X.take 19) m :=
  eqAt_relocAt _ X m h

theorem eqAbove_take_self (ν b : ℕ) (x : List E) (hb : b >>> ν = 0) :
    (⟨ν, b⟩ : VPlacement).eqAbove (x.take ν) = 1 := by
  rw [eqAbove_eqAt, List.drop_eq_nil_of_le (by simp)]
  rfl

/-- **A block of `C_main` inside the stream block at `S`** against the relocated block of the 19-variable cube. -/
theorem eqAbove_relocAt (S : ℕ) (x : List E) (k b o : ℕ) (hk : k ≤ 19)
    (h1 : b >>> k >>> (23 - k) = 0) (h2 : (b >>> k) % 2 ^ (19 - k) = (o >>> k) % 2 ^ (19 - k))
    (h3 : b >>> k >>> (19 - k) = S >>> 19) :
    (⟨23, 0⟩ : VPlacement).eqAbove x * (⟨k, b⟩ : VPlacement).eqAbove (x.take 23) =
      (⟨19, S⟩ : VPlacement).eqAbove x *
        ((⟨19, 0⟩ : VPlacement).eqAbove (x.take 19) * (⟨k, o⟩ : VPlacement).eqAbove (x.take 19)) := by
  rw [eqAbove_take_self 19 0 x rfl, one_mul]
  simp only [eqAbove_eqAt]
  have e1 : eqAt (x.drop k) (b >>> k) = eqAt ((x.take 23).drop k) (b >>> k) * eqAt (x.drop 23) 0 := by
    rw [eqAt_split_hi (x.drop k) _ (23 - k), h1, List.drop_take, List.drop_drop,
      show k + (23 - k) = 23 by omega]
  have e2 : eqAt (x.drop k) (b >>> k) =
      eqAt ((x.take 19).drop k) (o >>> k) * eqAt (x.drop 19) (S >>> 19) := by
    rw [eqAt_split_hi (x.drop k) _ (19 - k), h3, List.drop_take, List.drop_drop,
      show k + (19 - k) = 19 by omega, eqAt_mod ((x.drop k).take (19 - k)) (b >>> k),
      eqAt_mod ((x.drop k).take (19 - k)) (o >>> k)]
    congr 2
    have hl : ((x.drop k).take (19 - k)).length ≤ 19 - k := by simp
    have hd : 2 ^ ((x.drop k).take (19 - k)).length ∣ 2 ^ (19 - k) := Nat.pow_dvd_pow 2 hl
    rw [← Nat.mod_mod_of_dvd (b >>> k) hd, h2, Nat.mod_mod_of_dvd _ hd]
  show eqAt (x.drop 23) (0 >>> 23) * eqAt ((x.take 23).drop k) (b >>> k) = _
  rw [Nat.zero_shiftRight, mul_comm, ← e1, e2]
  ring

/-- **A block of `C_main` inside `S`** (`eqAbove_relocAt` at M′'s `S`). -/
theorem eqAbove_reloc (x : List E) (k b o : ℕ) (hk : k ≤ 19)
    (h1 : b >>> k >>> (23 - k) = 0) (h2 : (b >>> k) % 2 ^ (19 - k) = (o >>> k) % 2 ^ (19 - k))
    (h3 : b >>> k >>> (19 - k) = CMain.sOff20 >>> 19) :
    (⟨23, 0⟩ : VPlacement).eqAbove x * (⟨k, b⟩ : VPlacement).eqAbove (x.take 23) =
      (⟨19, CMain.sOff20⟩ : VPlacement).eqAbove x *
        ((⟨19, 0⟩ : VPlacement).eqAbove (x.take 19) * (⟨k, o⟩ : VPlacement).eqAbove (x.take 19)) :=
  eqAbove_relocAt _ x k b o hk h1 h2 h3

/-- **`⟨19, S⟩`'s point claim** is the relocated point claim on `C_rec`'s cube. -/
theorem relocS_point (z : List E) (v : E) :
    (BClaim.point ⟨19, CMain.sOff20⟩ z v).onStack = relocS (BClaim.point ⟨19, 0⟩ z v).onStack := by
  refine Prod.ext (funext fun x ↦ ?_) rfl
  show (⟨19, CMain.sOff20⟩ : VPlacement).eqAbove x * LeanVM.Protocol.Verifier.eqEval z (x.take 19) =
    (⟨19, CMain.sOff20⟩ : VPlacement).eqAbove x *
      ((⟨19, 0⟩ : VPlacement).eqAbove (x.take 19) * LeanVM.Protocol.Verifier.eqEval z ((x.take 19).take 19))
  rw [eqAbove_take_self 19 0 x rfl, one_mul, List.take_take, min_self]

end Lvm.VEq
