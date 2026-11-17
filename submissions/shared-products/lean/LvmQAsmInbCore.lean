-- New for lvm (INB): `interp.inb` from a memory on which every row holds and every `readd`
-- address lies in its region. The fold follows WP-10's `fold_spec` (`LvmLoopInterp`); the segment
-- predicate `SegsIn` and its program bridge are WP-11b-QL's `SegsAssert`/`asserts_iff`/`group_assert`
-- (`LvmQBuildSem`) with `RowAssert` replaced by the region condition.
import LvmQBuildLemmas

-- (GOLF2: 27 declarations that `certified` does not use moved verbatim to `LvmQAsmInbOff`, outside its import closure.)

/-!
# Every `readd` finds its cell

`RdIn M i`: if instance `i` is a `readd lo m`, its address operand's value in `M` is `g^(lo + k)` for
some `k < 2^m`.

* **`inb_of_mem`**: a memory with the inputs on which every row relation holds (`Holds`) and every
  `readd` address is in its region gives `(Q.interp inK inE).inb = true` (with `wf`, the input sizes
  and `GInj`). No `inb` is assumed: the interpreter agrees with `M` below its clock, so it computes
  the address `M` has, and `findExp` finds it.
* **`SegsIn M p δ`**: `RdIn` for every instance of the segments `δ` at `p` (the builder form);
  `segsIn_append`, `in_bind`, **`toProgram_in`** (`SegsIn` of a gadget's segments ⇒ `RdIn` on every
  instance of `toProgram`), `segsIn_of_noReadd` (segments without `readd`, by `decide`).
* **`InOk M m`**: for every pointer, the gadget's rows holding imply its `readd`s are in region;
  closed under `bind`, `seqAll`, `pure`.
-/

set_option autoImplicit false

namespace Lvm.Loop

open FE

/-- **The region condition of an instance**: a `readd lo m`'s address is `g^(lo + k)`, `k < 2^m`. -/
def RdIn (M : Mem) (i : Inst) : Prop :=
  match i.row.op with
  | .readd lo m => ∃ k < 2 ^ m, FK.x ^ (lo + k) = (M.arg i 0).c₀
  | _ => True

namespace Program

variable (Q : Program)

/-! ## The interpreter keeps its inputs (no `inb` needed) -/

theorem step_kc (s : St) (i : Inst) : (Q.step s i).kc = s.kc ∨ ∃ v, (Q.step s i).kc = s.kc.push v := by
  have hput : ∀ (τ : Ty) (v : FE), (s.put τ v).kc = s.kc ∨ ∃ w, (s.put τ v).kc = s.kc.push w := by
    intro τ v; cases τ
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  rcases hop : i.row.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo, m⟩ | ⟨f, hh⟩ <;> simp only [step, hop]
  rotate_right
  · exact hput _ _
  · exact hput _ _
  · exact hput _ _
  · simp
  · exact hput _ _
  · exact hput _ _
  · split
    · exact hput _ _
    · rcases hput i.row.ty 0 with h | h
      · exact Or.inl h
      · exact Or.inr h

end Program

namespace Build

/-! ## Segments -/

/-! ## Segments without `readd` -/

/-- A row that is not a `readd`. -/
def rowNoRd (r : Row) : Bool := match r.op with | .readd .. => false | _ => true

theorem rdIn_of_noRd {M : Mem} {i : Inst} (h : rowNoRd i.row = true) : RdIn M i := by
  unfold RdIn; unfold rowNoRd at h
  split
  · next _ _ hop => rw [hop] at h; simp at h
  · trivial

/-! ## Gadgets whose rows put their `readd`s in region -/

/-- A loop row's region condition, on the resolved operand (as `LRel`). -/
theorem loop_in_iff (M : Mem) (o : LoopOut) (jf t : Nat) :
    RdIn M (instAt o.p o.blk jf t) ↔
      match (o.tpl.getD t default).op with
      | .readd lo m => ∃ k < 2 ^ m, FK.x ^ (lo + k) = (o.arg M jf t 0).c₀
      | _ => True := by
  have hrow : (instAt o.p o.blk jf t).row = resRow o.p o.dims o.tpl (o.tpl.getD t default) :=
    mkLoop_row _ _ _ _
  unfold RdIn
  rw [hrow]
  simp only [resRow, instAt_loop_arg]

end Build

end Lvm.Loop
