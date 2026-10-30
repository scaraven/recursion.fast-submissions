-- G6: `FRXField`'s controls (`Controls`), moved here verbatim from `FRXField` to keep them off `Solution`'s
-- import closure (stage G6); `FR` imports this module.
import FRXField

namespace FR.X

open RecursionFast Polynomial BinaryField B64
variable {I : Array Word} {s : St}

/-! ## Controls (kernel-checked)

Programs that read their operands from the tape into registers `64 …`, run one routine and
output the result, run by the contract's interpreter (`XProg.run`) with `260` memory words. The
`F` and `K` operands and products are `FRFieldControls`' first KAT (S-A's independent
schoolbook reference, `probe/fr-field/kat.py`).

* Positive: `mulF`, `mulK` give the KAT products (`mulF_kat`, `mulK_kat`); `invK_guard`
  instantiates `invK_sem` at a nonzero operand. Squares and inverses are covered by their
  `*_sem` theorems (kernel-evaluating them through the contract's `Fin.foldl` `clmul` costs
  ≈ 15 s; their value KATs are measurements in `logs/S-H1/stepcount.log`).
* **The measured step count of one `F` product**: the program that is only `mulF` halts with
  `260 + 65` fuel and not with `260 + 64` (`mulF_alone`): `8` for the prologue and `57`, the
  `steps_mulF` count.
* Negative: with the reduction constant cell overwritten (a program that is not `WF`), `mulF`
  does not give the product (`mulF_bad_const`): the invariant is needed.
-/

namespace Controls

/-- Read `n` tape words into registers `base …`. -/
def readN (base : ℕ) : ℕ → XIR
  | 0 => .blk []
  | k + 1 => .seq (readN base k) (.seq (.blk [.const 120 (BitVec.ofNat 64 k)]) (.input (base + k)
      120))

/-- Output registers `base … base + n − 1`. -/
def outN (base : ℕ) : ℕ → XIR
  | 0 => .blk []
  | k + 1 => .seq (outN base k) (.out (base + k))

/-- Read two `n`-word operands into `64 …`, run `op`, output `n` words from `64 + 2n`. -/
def binProg (n : ℕ) (op : XIR) : XIR := .seq (readN 64 (2 * n)) (.seq op (outN (64 + 2 * n) n))

/-- `FRFieldControls`' first `F` KAT operands. -/
def tF : List Word := [0x0CC65817272B53A4, 0x2120FC8CCEE55FE9, 0x99363C9930CF43AC,
    0x6889C91E3005A706]

/-- `FRFieldControls`' first `K` KAT operands. -/
def tK : List Word := [0x2641940B4DF62868, 0xC0450C5C86166DEC, 0x5298E4BB63FE5590,
  0x5DB1608995CCB6A0, 0x95E30255B5D45D27, 0x18B2BF46EE11E992, 0x91782A4F625E5555,
  0xB49F8D70989DA94A]

theorem mulF_kat : (toProg 260 0 (binProg 2 (mulF 68 64 66))).run tF 400 =
    some [0x6BDB7CDE7A2DD504, 0x24D581B7235CF4BE] := by decide +kernel

theorem mulF_alone : (toProg 260 0 (mulF 68 64 66)).run [] (260 + 65) = some [] ∧
    (toProg 260 0 (mulF 68 64 66)).run [] (260 + 64) = none := by decide +kernel

theorem mulF_bad_const : (toProg 260 0 (.seq (.blk [.const cRed 0x1D])
    (binProg 2 (mulF 68 64 66)))).run tF 400 ≠ some [0x6BDB7CDE7A2DD504, 0x24D581B7235CF4BE] := by
  decide +kernel

theorem mulK_kat : (toProg 260 0 (binProg 4 (mulK 72 64 68))).run tK 800 =
    some [0xA7076D7E76A71A45, 0xB6C9CAE676ACD4CA, 0x423E1CBA3D46D2A5, 0xFBB4F8964518C30E] := by
  decide +kernel

/-- A state satisfying `Inv` with the `K` element `1` in registers `64 … 67`. -/
def oneK : St := ⟨(initSt 260).M.setIfInBounds 64 1, #[]⟩

/-- `invK_sem`'s hypotheses hold at a nonzero operand (`1`): a guard; the `K` inverse's run
(1,379 steps) is not evaluated by the kernel, its value KAT is a measurement
(`logs/S-H1/stepcount.log`). -/
theorem invK_guard (I : Array Word) : rdK oneK.M 64 = 1 ∧
    rdK (semXIR I (invK 68 64) oneK).M 68 = (rdK oneK.M 64)⁻¹ := by
  have hM : Inv oneK.M := by
    simp only [oneK]
    exact inv_of_frame (inv_initSt (by decide)) (size_set ..) fun j hj => rd_set_ne (by omega)
  exact ⟨by decide +kernel, invK_sem hM (by decide) (by decide) (by decide)⟩

end Controls

end FR.X
