-- New for lvm2 roll 11 (M′, R11-IR): the relocation of a `C_rec` stack claim onto `C_main`'s stream block `S`
-- (`relocS`, the language side of `LvmCertM20.relocB20`) and the closed forms that tie V_S's `C_main` claims on `S`
-- (the relayout's point claim, the `KS` link's `M`, `σ′`'s region claim) to the relocated spec claims.
import LvmVEqMid
import LvmEqLemmas
import LvmLayoutArith
import LvmRingFidelity

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

theorem relocS_apply (c : VStackClaim) (x : List E) :
    (relocS c).1 x = (⟨19, CMain.sOff20⟩ : VPlacement).eqAbove x * c.1 (x.take 19) := rfl

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

/-- **A word of `S`**: `eq(X, m) = sel_S(X) · eq(X_{<19}, m)` when `m` and `S` agree above bit 19. -/
theorem eqAt_reloc (X : List E) (m : ℕ) (h : m >>> 19 = CMain.sOff20 >>> 19) :
    eqAt X m = (⟨19, CMain.sOff20⟩ : VPlacement).eqAbove X * eqAt (X.take 19) m := by
  rw [eqAbove_eqAt, eqAt_split_hi X m 19, h]
  exact mul_comm _ _

theorem eqAbove_take_self (ν b : ℕ) (x : List E) (hb : b >>> ν = 0) :
    (⟨ν, b⟩ : VPlacement).eqAbove (x.take ν) = 1 := by
  rw [eqAbove_eqAt, List.drop_eq_nil_of_le (by simp)]
  rfl

/-- **A block of `C_main` inside `S`** against the relocated block of the 19-variable cube. -/
theorem eqAbove_reloc (x : List E) (k b o : ℕ) (hk : k ≤ 19)
    (h1 : b >>> k >>> (23 - k) = 0) (h2 : (b >>> k) % 2 ^ (19 - k) = (o >>> k) % 2 ^ (19 - k))
    (h3 : b >>> k >>> (19 - k) = CMain.sOff20 >>> 19) :
    (⟨23, 0⟩ : VPlacement).eqAbove x * (⟨k, b⟩ : VPlacement).eqAbove (x.take 23) =
      (⟨19, CMain.sOff20⟩ : VPlacement).eqAbove x *
        ((⟨19, 0⟩ : VPlacement).eqAbove (x.take 19) * (⟨k, o⟩ : VPlacement).eqAbove (x.take 19)) := by
  rw [eqAbove_take_self 19 0 x rfl, one_mul]
  simp only [eqAbove_eqAt]
  have e1 : eqAt (x.drop k) (b >>> k) = eqAt ((x.take 23).drop k) (b >>> k) * eqAt (x.drop 23) 0 := by
    rw [eqAt_split_hi (x.drop k) _ (23 - k), h1, List.drop_take, List.drop_drop,
      show k + (23 - k) = 23 by omega]
  have e2 : eqAt (x.drop k) (b >>> k) =
      eqAt ((x.take 19).drop k) (o >>> k) * eqAt (x.drop 19) (CMain.sOff20 >>> 19) := by
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

/-- **`⟨19, S⟩`'s point claim** is the relocated point claim on `C_rec`'s cube. -/
theorem relocS_point (z : List E) (v : E) :
    (BClaim.point ⟨19, CMain.sOff20⟩ z v).onStack = relocS (BClaim.point ⟨19, 0⟩ z v).onStack := by
  refine Prod.ext (funext fun x ↦ ?_) rfl
  show (⟨19, CMain.sOff20⟩ : VPlacement).eqAbove x * LeanVM.Protocol.Verifier.eqEval z (x.take 19) =
    (⟨19, CMain.sOff20⟩ : VPlacement).eqAbove x *
      ((⟨19, 0⟩ : VPlacement).eqAbove (x.take 19) * LeanVM.Protocol.Verifier.eqEval z ((x.take 19).take 19))
  rw [eqAbove_take_self 19 0 x rfl, one_mul, List.take_take, min_self]

/-- A sum claim's part moved by `S`. -/
def shiftS (q : E × VPlacement × List E) : E × VPlacement × List E :=
  (q.1, ⟨q.2.1.variableCount, CMain.sOff20 + q.2.1.index⟩, q.2.2)

/-- **A sum claim on `C_main` whose parts lie in `S`** is the relocated sum claim on `C_rec`'s cube. -/
theorem relocS_sum (parts : List (E × VPlacement × List E)) (v : E)
    (hp : ∀ q ∈ parts, q.2.1.variableCount ≤ 19 ∧
      (CMain.sOff20 + q.2.1.index) >>> q.2.1.variableCount >>> (23 - q.2.1.variableCount) = 0 ∧
      ((CMain.sOff20 + q.2.1.index) >>> q.2.1.variableCount) % 2 ^ (19 - q.2.1.variableCount) =
        (q.2.1.index >>> q.2.1.variableCount) % 2 ^ (19 - q.2.1.variableCount) ∧
      (CMain.sOff20 + q.2.1.index) >>> q.2.1.variableCount >>> (19 - q.2.1.variableCount) =
        CMain.sOff20 >>> 19) :
    (sumClaimE 23 (parts.map shiftS) v).onStack = relocS (sumClaimE 19 parts v).onStack := by
  refine Prod.ext (funext fun x ↦ ?_) rfl
  show (⟨23, 0⟩ : VPlacement).eqAbove x * LeanVM.Protocol.Verifier.sumE ((parts.map shiftS).map fun (c, blk, z) ↦
      c * blk.eqAbove (x.take 23) * LeanVM.Protocol.Verifier.eqEval z ((x.take 23).take blk.variableCount)) =
    (⟨19, CMain.sOff20⟩ : VPlacement).eqAbove x * ((⟨19, 0⟩ : VPlacement).eqAbove (x.take 19) *
      LeanVM.Protocol.Verifier.sumE (parts.map fun (c, blk, z) ↦
        c * blk.eqAbove ((x.take 19).take 19) *
          LeanVM.Protocol.Verifier.eqEval z (((x.take 19).take 19).take blk.variableCount)))
  rw [eqAbove_take_self 19 0 x rfl, one_mul, List.take_take, min_self, LeanVM.Protocol.Whir.Complete.sumE_eq,
    LeanVM.Protocol.Whir.Complete.sumE_eq, List.map_map, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun q hq ↦ ?_)
  obtain ⟨c, ⟨k, o⟩, z⟩ := q
  obtain ⟨hk, h1, h2, h3⟩ := hp _ hq
  dsimp only [Function.comp, shiftS] at h1 h2 h3 hk ⊢
  have e := eqAbove_reloc x k (CMain.sOff20 + o) o hk h1 h2 h3
  rw [eqAbove_take_self 19 0 x rfl, one_mul] at e
  rw [List.take_take, List.take_take, min_eq_left (by omega : k ≤ 23), min_eq_left hk]
  calc (⟨23, 0⟩ : VPlacement).eqAbove x * (c * (⟨k, CMain.sOff20 + o⟩ : VPlacement).eqAbove (x.take 23) *
        LeanVM.Protocol.Verifier.eqEval z (x.take k))
      _ = c * ((⟨23, 0⟩ : VPlacement).eqAbove x * (⟨k, CMain.sOff20 + o⟩ : VPlacement).eqAbove (x.take 23)) *
        LeanVM.Protocol.Verifier.eqEval z (x.take k) := by ring
      _ = _ := by rw [e]; ring

end Lvm.VEq
