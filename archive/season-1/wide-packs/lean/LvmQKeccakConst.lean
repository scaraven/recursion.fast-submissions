import LvmDecideKeccak
import LvmKeccakRmfeLit

/-!
# QA1: the RMFE constants as literals (`rmfeProject`, `rmfeEmbed`, kernel-checked)

Values of `ref/loopir.py` (`RMFE_PROJECT`, `RMFE_EMBED`, leanVM `keccak.rs:25-46`), equal to
`F`'s computed lists. `F`'s `rmfe` (`LvmDecideKeccak`) and the verifier language's
(`Verifier.rmfe`, `LvmVCore`) have the same definition: `rmfe_eq_V` proves them equal piece by
piece, without evaluating either, so the kernel evaluates `rmfe` once, in
`KeccakGkr.rmfeProject_eq` (`LvmKeccakRmfeLit`), and `rmfeProject_eq`, `rmfeEmbed_eq` here (and
`Lvm.VEq.rmfeProject_eq`, `rmfeEmbed_eq`) are read off it.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm LeanVM.Protocol

/-- `RMFE_PROJECT` as a literal. -/
def projLit : List Nat := [0x1, 0x1ffffffffffffffffffffffffff, 0x1a74e9d3a74e9d3a74e9d3a74e9,
  0x9d3a74e9d3a74e9d3a74e9d3a7, 0xe5cb972e5cb972e5cb972e5cb9, 0x5cb972e5cb972e5cb972e5cb97,
  0x1a42bb1f3485763e690aec7cd21, 0x163e690aec7cd215d8f9a42bb1f, 0xd215d8f9a42bb1f3485763e690,
  0x1d4259f1ba84b3e3750967c6ea1, 0xb3e3750967c6ea12cf8dd4259f, 0xea12cf8dd4259f1ba84b3e3750,
  0xb4327dc56864fb8ad0c9f715a1, 0x193ee2b4327dc56864fb8ad0c9f, 0x15a193ee2b4327dc56864fb8ad0,
  0x19c3522fb386a45f670d48bece1, 0x8bece1a917d9c3522fb386a45f, 0xce1a917d9c3522fb386a45f670,
  0xac39be8958737d12b0e6fa2561, 0x19be8958737d12b0e6fa2561cdf, 0x561cdf44ac39be8958737d12b0,
  0x4c2d477c985a8ef930b51df261, 0x3be4c2d477c985a8ef930b51df, 0x12616a3be4c2d477c985a8ef930,
  0xdb6db6db6db6db6db6db6db6db, 0x1d647ac8f591eb23d647ac8f591, 0xb23d647ac8f591eb23d647ac8f,
  0x6bc4d789af135e26bc4d789af1, 0x26bc4d789af135e26bc4d789af, 0x118c6318c6318c6318c6318c631,
  0xf7bdef7bdef7bdef7bdef7bdef, 0x100000000000000000000000000]

/-- `RMFE_EMBED` as a literal. -/
def embedLit : List Nat := [0xabfea80157fd5, 0xcd54cffe65566, 0xd001a001a0034, 0x9ffec0013ffd8,
  0xe801d001d003a, 0xb00160016002c, 0x65edfba880e5c, 0x8be262ce9a10e, 0xcbdbf75101cb8, 0x465b58f9289d0,
  0xb6c6a0afaa406, 0x8cb6b1f2513a0, 0xfc404b5027a68, 0x652b4261a06d6, 0xaf7dc6a2e0b7a, 0xfd4ee39a12084,
  0x64df8d127959e, 0xad6097368bea2, 0x64799352e740a, 0x8afa2d9d20d6a, 0xc8f326a5ce814, 0xd6c0b0c85a94c,
  0x562bef71f64ee, 0xfa7c31921ad32, 0x71247000e248e, 0xa09bb00141376, 0xc0ed200181da4, 0x53d6e000a7adc,
  0x629b4000c5368, 0x63de3000c7bc6, 0x4294200085284, 0x157fd5002affaa]

/-! ## `F`'s embedding is the verifier language's, piece by piece -/

theorem bitLength_eq_V : Lvm.bitLength = Verifier.bitLength := rfl

theorem productBits_eq_V : Lvm.productBits = Verifier.productBits := rfl

theorem rmfeFactors_eq_V : Lvm.rmfeFactors = Verifier.rmfeFactors := rfl

theorem carrylessAux_eq_V : Lvm.carrylessAux = Verifier.carrylessAux := by
  funext fuel a b out
  induction fuel generalizing a b out with
  | zero => rfl
  | succ n ih => simp only [Lvm.carrylessAux, Verifier.carrylessAux, ih]

theorem carryless_eq_V : Lvm.carryless = Verifier.carryless := by
  funext a b; simp only [Lvm.carryless, Verifier.carryless, carrylessAux_eq_V]

theorem carrylessDivmodAux_eq_V : Lvm.carrylessDivmodAux = Verifier.carrylessDivmodAux := by
  funext fuel f q a
  induction fuel generalizing q a with
  | zero => rfl
  | succ n ih => simp only [Lvm.carrylessDivmodAux, Verifier.carrylessDivmodAux, ih, bitLength_eq_V]

theorem carrylessDivmod_eq_V : Lvm.carrylessDivmod = Verifier.carrylessDivmod := by
  funext a f
  simp only [Lvm.carrylessDivmod, Verifier.carrylessDivmod, carrylessDivmodAux_eq_V, bitLength_eq_V]

theorem bitParity_eq_V : Lvm.bitParity = Verifier.bitParity := by
  funext n; simp only [Lvm.bitParity, Verifier.bitParity, bitLength_eq_V]

theorem rmfeModulus_eq_V : Lvm.rmfeModulus = Verifier.rmfeModulus := by
  unfold Lvm.rmfeModulus Verifier.rmfeModulus; rw [rmfeFactors_eq_V, carryless_eq_V]; rfl

theorem rmfeFactor_eq_V : Lvm.rmfeFactor = Verifier.rmfeFactor := by
  funext m f b
  simp only [Lvm.rmfeFactor, Verifier.rmfeFactor, carryless_eq_V, carrylessDivmod_eq_V, bitParity_eq_V,
    productBits_eq_V, bitLength_eq_V]

/-- `F`'s `rmfe` is `Verifier.rmfe`. -/
theorem rmfe_eq_V : Lvm.rmfe = Verifier.rmfe := by
  unfold Lvm.rmfe Verifier.rmfe; rw [rmfeFactor_eq_V, rmfeModulus_eq_V, rmfeFactors_eq_V, productBits_eq_V]

/-! ## The literals -/

theorem rmfeProject_eq : rmfeProject = projLit :=
  (congrArg Prod.snd rmfe_eq_V).trans KeccakGkr.rmfeProject_eq

theorem rmfeEmbed_eq : rmfeEmbed = embedLit :=
  (congrArg Prod.fst rmfe_eq_V).trans KeccakGkr.rmfeEmbed_eq

end Lvm.Q1
