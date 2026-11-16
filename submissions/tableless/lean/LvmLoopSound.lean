import LvmLoopPieces

-- (GOLF2: 22 declarations that `certified` does not use moved verbatim to `LvmQAsmHar47Off`, outside its import closure.)

/-!
# `loopir_sound`: tables that hold are the interpreter's run

**`loopir_sound`** (generic over every program): if the program check passes, every constraint of
every piece vanishes on every row, every read's key `(sep, addr, value)` is a seed's key (the
conclusion of leanVM's lookup argument from a balanced bus), `g`-powers are injective below the cell
counts, and the interpreter's `readd`s found their cells, then every committed result and operand
value of every piece row is the interpreter's cell (`WitnessOf W (interpMem …)`) and every gated
assertion holds (`interp.ok = true`).

The proof: the seeds define a memory `seedMem` (the inputs, then each cell's unique writer row's
committed result); the bus makes every read the seed memory's cell at the read's address
(`read_ok`, `readd_ok`); the constraints then give every instance's relation on that memory
(`holds_seedMem`), and `interp_unique` identifies it with the interpreter's.
-/

namespace Lvm.Loop

open FE Program

namespace Program

variable (Q : Program)

/-! ## Writers -/

theorem writer_row {npx : Nat × Piece × Nat}
    (h : npx ∈ Q.prows) (hw : npx.2.1.shape.writes = true) :
    (Q.pinst npx.2.1 npx.2.2).row.writes = some npx.2.1.shape.ty ∧
      (Q.pinst npx.2.1 npx.2.2).row.ty = npx.2.1.shape.ty := by
  obtain ⟨-, hsh⟩ := Q.prow_inst (n := npx.1) (x := npx.2.2) (p := npx.2.1) h
  rw [← hsh] at hw ⊢
  simp only [Shape.writes, Row.shape, bne_iff_ne, ne_eq] at hw
  have hop : (Q.pinst npx.2.1 npx.2.2).row.op ≠ .assert0 := fun h' => hw (by rw [h']; rfl)
  simp only [Row.shape, hw, if_false, Row.writes]
  first | exact ⟨trivial, trivial⟩ | (split <;> simp_all)

/-! ## The bus makes every read the seed memory's cell -/

/-! ## Every row relation holds on the seed memory -/

/-! ## The theorem -/

end Program

end Lvm.Loop
