-- New for lvm (WP-14a): the P20 commitment table of the compiled verifier and the relations between
-- V_S's claims (`FE`) and the verifier language's (`E`), shared by the per-phase refinements.
import LvmVEqPrim
import LvmVEqMid
import LvmVEqPhases

/-!
# P20's commitments; native and language claims

* `capS` (= WP-14's `capOfS`: cap level 8 for `C_main`'s root of `2^19` leaves (lvm2 S2), 7 otherwise),
  `shpS` (M′: the three commitments in commit order, `C_main`'s root `(19, 64)` and its levels 1–2
  `(16, 48)`, `(13, 48)`), `idxS` (an oracle's commitment index);
* `BCRel c c'`: a native block claim and a language block claim (`LvmVEqMid.BClaim`) agree: same
  block, value and weight through `FE.toExt3` (the weight on every image point);
  `CRel` with the commitment; `SCRel` for stack claims.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm

/-- The cap level of a tree of `2^ht` leaves at P20 (WP-14's `capOfS`). -/
def capS (ht _w : ℕ) : ℕ := if ht = 19 then 8 else 7

/-- The occupied words of a commitment of `2^ht` rows of `w` words at P20 (`LvmCertS.occOfS`): `47`
for `C_main`'s root (both shapes; M′ `S2GM`, B1 had 46), `35` for `C_rec`'s (B1 only; unused at M′), the whole
row otherwise. -/
def occS (ht w : ℕ) : ℕ := if ht = 19 ∧ w = 64 then 47 else if ht = 15 ∧ w = 64 then 35 else w

/-- The three commitments' shapes `(height, width)` in commit order at P20 (lvm2 roll 11, M′ `S2GM`: one
commitment, `C_main`'s root and its WHIR levels 1–2; B1 had `C_rec`'s root and level 1 at 1, 2). -/
def shpS : ℕ → ℕ × ℕ
  | 0 => (19, 64)
  | 1 => (16, 48)
  | _ => (13, 48)

/-- An oracle's commitment index (M′: `C_main`'s level `j` at `j`, WHIR's `cidx` with `n₀ = 1`; `C_rec` has no
oracle at M′, its references are sent past the table). -/
def idxS : Ref → ℕ
  | ⟨.main, j⟩ => j
  | ⟨.crec, j⟩ => j + 100 -- unreachable at M′: no `C_rec` item is left in the schedule

/-- Refinement at P20's commitment table. -/
abbrev Ref20 {α β : Type} (sig : ByteArray) (d : DM β) (P : LeanVM.Protocol.Compile.VerifierProgram α)
    (R : β → α → Prop) : Prop := RefAt capS occS shpS sig d P R

/-- A native block claim and a language block claim agree. -/
def BCRel (c : Lvm.BlockClaim) (c' : BClaim) : Prop :=
  c'.block = ⟨c.block.variableCount, c.block.index⟩ ∧ c'.value = FE.toExt3 c.value ∧
    ∀ xs : List FE, c'.weight (xs.map FE.toExt3) = FE.toExt3 (c.weight xs)

/-- With the commitment. -/
def CRel (a : Com × Lvm.BlockClaim) (b : Com × BClaim) : Prop := a.1 = b.1 ∧ BCRel a.2 b.2

/-- A native stack claim and a language stack claim agree. -/
def SCRel (c : Lvm.StackClaim) (c' : VStackClaim) : Prop :=
  c'.2 = FE.toExt3 c.2 ∧ ∀ xs : List FE, c'.1 (xs.map FE.toExt3) = FE.toExt3 (c.1 xs)

end Lvm.VEq
