-- New for `flock-recursive` (BLUEPRINT §5.6, row "F, K fields and twins"); the pattern of
-- `submissions/spartan-srom/lean/SpartanSromFieldControls.lean`. The known answers are printed by
-- `probe/fr-field/kat.py` (an independent schoolbook reference in Python, seed 20261027) and this
-- file by `probe/fr-field/gen_controls.py`.
import FRField256

/-!
# Controls for the field layer

Kernel-checked evaluations of the compiled operations, positive and negative. They pin what a wrong
constant would silently change: the constants `β = x^63` and `α = β y`, the Karatsuba and lazy
reduction of `F.mul`, the reduction `u^2 = u + α` of `K.mul`, the inverses and the byte order. The
negative controls show that the trace hypothesis of `quadratic_irreducible` is needed: the
trace-zero constant `1` gives `y^2 + y + 1`, which has a root in `GF(2^64)` and is reducible.
-/

namespace FR.FieldControls

open FR Polynomial

/-! ## Products against the independent reference -/

/-- Eight `F` triples `(a, b, a b)` of the reference (schoolbook product, `y^2 = y + x^63`). -/
def katF : List (F × F × F) := [
  (⟨⟨0x0CC65817272B53A4⟩, ⟨0x2120FC8CCEE55FE9⟩⟩,
    ⟨⟨0x99363C9930CF43AC⟩, ⟨0x6889C91E3005A706⟩⟩,
    ⟨⟨0x6BDB7CDE7A2DD504⟩, ⟨0x24D581B7235CF4BE⟩⟩),
  (⟨⟨0x3A31AADC19E3ECBF⟩, ⟨0x071674EE0693E0D9⟩⟩,
    ⟨⟨0x6BE1E08A7E114E68⟩, ⟨0x8DE424016B820FE4⟩⟩,
    ⟨⟨0x244BC9B01462D3E5⟩, ⟨0xF3026AA4979DAC65⟩⟩),
  (⟨⟨0x0A727244D2A65227⟩, ⟨0x141337ACF1E2B441⟩⟩,
    ⟨⟨0x6EDE80A3BA89E31D⟩, ⟨0xC6C4EE2E3B9EFAD5⟩⟩,
    ⟨⟨0x43BFB2E669825116⟩, ⟨0x8467CA181C3F98D6⟩⟩),
  (⟨⟨0xBE6FA6127EA696C3⟩, ⟨0xE25C7C4AE65CB5DB⟩⟩,
    ⟨⟨0x3500F48AB489CB10⟩, ⟨0x62734460417AE7FB⟩⟩,
    ⟨⟨0x196AF3312759DBBB⟩, ⟨0x1F8A3C54929ACFFC⟩⟩),
  (⟨⟨0x2C442A3AD00F1436⟩, ⟨0x7C3C2F9F335B53E5⟩⟩,
    ⟨⟨0x53976270C78E175D⟩, ⟨0x213B6DA5685F71AE⟩⟩,
    ⟨⟨0x7221CD99AFCD97CD⟩, ⟨0x57FB40AF14D4B13F⟩⟩),
  (⟨⟨0x5E4C955942756822⟩, ⟨0xF428D119E3DFF133⟩⟩,
    ⟨⟨0x1674844A519AABEC⟩, ⟨0xD64A860802F38533⟩⟩,
    ⟨⟨0x2985AE2715D2C9A3⟩, ⟨0x4D1D9F8365A7AD5E⟩⟩),
  (⟨⟨0x1E0E94DACDCA2A59⟩, ⟨0x36F2F503A871DFF9⟩⟩,
    ⟨⟨0xF18D6C4DEB6AF134⟩, ⟨0xEB03A85E443884FC⟩⟩,
    ⟨⟨0x16F1BD1FF2CFF07F⟩, ⟨0x664115F41524AF2A⟩⟩),
  (⟨⟨0x9063204D4E6752C1⟩, ⟨0x8A97BB29A59B03D7⟩⟩,
    ⟨⟨0x3056DFADA05552BE⟩, ⟨0x1562FBD6451163B3⟩⟩,
    ⟨⟨0x7629E63DF7DC3402⟩, ⟨0x4DF4929E6F052775⟩⟩)]

/-- **The eight `F` products agree with the reference.** -/
theorem mul_kat_F : katF.map (fun t => t.1 * t.2.1) = katF.map (·.2.2) := by decide +kernel

/-- The reference's first product with the plausible wrong constant `β = x^61`. -/
def wrongF : F := ⟨⟨0x4B762434B65FB2CA⟩, ⟨0x24D581B7235CF4BE⟩⟩

/-- Negative: the first product is not the one with `β = x^61`. -/
theorem mul_kat_F_ne : katF[0]!.1 * katF[0]!.2.1 ≠ wrongF := by decide +kernel

/-- Eight `K` triples `(a, b, a b)` of the reference (`u^2 = u + β y`). -/
def katK : List (K × K × K) := [
  (⟨⟨⟨0x2641940B4DF62868⟩, ⟨0xC0450C5C86166DEC⟩⟩, ⟨⟨0x5298E4BB63FE5590⟩, ⟨0x5DB1608995CCB6A0⟩⟩⟩,
    ⟨⟨⟨0x95E30255B5D45D27⟩, ⟨0x18B2BF46EE11E992⟩⟩, ⟨⟨0x91782A4F625E5555⟩, ⟨0xB49F8D70989DA94A⟩⟩⟩,
    ⟨⟨⟨0xA7076D7E76A71A45⟩, ⟨0xB6C9CAE676ACD4CA⟩⟩, ⟨⟨0x423E1CBA3D46D2A5⟩, ⟨0xFBB4F8964518C30E⟩⟩⟩),
  (⟨⟨⟨0xA52DD713B80A40B6⟩, ⟨0xFD252688627FD848⟩⟩, ⟨⟨0xC02AEDEBA2F6AA9E⟩, ⟨0xC83E8BAF538499D9⟩⟩⟩,
    ⟨⟨⟨0x5A875486E99ED6AE⟩, ⟨0xA087CC556F4BE6E8⟩⟩, ⟨⟨0x9AA80F8A49B4FA90⟩, ⟨0x24ADBA25E931A56F⟩⟩⟩,
    ⟨⟨⟨0x0D4F356658BF4069⟩, ⟨0xEBE1DC9188041AEF⟩⟩, ⟨⟨0xD462760B899E75C3⟩, ⟨0x3782A5182D0B1F9E⟩⟩⟩),
  (⟨⟨⟨0x3E60CA3809906D54⟩, ⟨0xE02071366047B633⟩⟩, ⟨⟨0x83FF7FE3E1F0859D⟩, ⟨0x564B1DD7CDEE32A2⟩⟩⟩,
    ⟨⟨⟨0xCBD2D4944CA05421⟩, ⟨0x9CB9557B327BD25B⟩⟩, ⟨⟨0x0F276F7FD5562BFA⟩, ⟨0xA24590AB86A403FD⟩⟩⟩,
    ⟨⟨⟨0xD6584FDCF9CF8D2B⟩, ⟨0xC5CDAAD8E827E37C⟩⟩, ⟨⟨0x5A5FCDDDE69A286E⟩, ⟨0x7BB481D0F11023C3⟩⟩⟩),
  (⟨⟨⟨0x9E6C6D9E859C2FBA⟩, ⟨0x3892543B0FDF7BC0⟩⟩, ⟨⟨0x792677BC063764FD⟩, ⟨0x219B5D8FF50BB9C4⟩⟩⟩,
    ⟨⟨⟨0x8B1E1BC8CD7CBF52⟩, ⟨0x20B98C04B7D04B52⟩⟩, ⟨⟨0x4C673AB53E2154AD⟩, ⟨0x3060D10A946FE4FF⟩⟩⟩,
    ⟨⟨⟨0xB753BA9F6745AF6E⟩, ⟨0xB70CEF74E349BC6D⟩⟩, ⟨⟨0x03021F07A81C9C81⟩, ⟨0x263CE689B68A5810⟩⟩⟩),
  (⟨⟨⟨0xF23A8FFAF0634524⟩, ⟨0x9377D946442173B3⟩⟩, ⟨⟨0x3985F9E7AC6C785B⟩, ⟨0xAFA98C2177F38F49⟩⟩⟩,
    ⟨⟨⟨0xA27D336DC4FC4FEA⟩, ⟨0x15A7DB7DF35032D8⟩⟩, ⟨⟨0x9874971FDCA0574D⟩, ⟨0x523798B489BE8404⟩⟩⟩,
    ⟨⟨⟨0x26A4964AFA48C3A9⟩, ⟨0xDF4AA5043F8618CF⟩⟩, ⟨⟨0x5EDF2AF0FA806412⟩, ⟨0xC7A9F0EE4BC23EFD⟩⟩⟩),
  (⟨⟨⟨0x88784399D488568F⟩, ⟨0x620149105780C65F⟩⟩, ⟨⟨0x67611E61FEDB3279⟩, ⟨0xFB6C68D5B547B182⟩⟩⟩,
    ⟨⟨⟨0xB03C81BC6773B421⟩, ⟨0xA704BAAD5793637E⟩⟩, ⟨⟨0x6681D9241DD87B27⟩, ⟨0x483F418A59675F13⟩⟩⟩,
    ⟨⟨⟨0x843DAFAD26A2C2C6⟩, ⟨0x01F5A9063C3BB2A2⟩⟩, ⟨⟨0x1807167468C6DA9D⟩, ⟨0xBE8B0756A2F8AC1B⟩⟩⟩),
  (⟨⟨⟨0xDEED24C57DCFA85A⟩, ⟨0x87EC348182DAD535⟩⟩, ⟨⟨0x85F6E63FE2CDE537⟩, ⟨0xFE38D6C201850D6B⟩⟩⟩,
    ⟨⟨⟨0x1DCB523513030A49⟩, ⟨0x3921ECA7874FE119⟩⟩, ⟨⟨0x779F589D84032702⟩, ⟨0x794EA4975B9652EF⟩⟩⟩,
    ⟨⟨⟨0x968603B5DE3EA199⟩, ⟨0xB9A22F9718C9AE37⟩⟩, ⟨⟨0xD473BFF6D9F0CA37⟩, ⟨0xA7AA1B7000878A69⟩⟩⟩),
  (⟨⟨⟨0x9471CDED08D7C8C0⟩, ⟨0x4B1D7C1F2A8446A5⟩⟩, ⟨⟨0xAE554A5B0F1521D0⟩, ⟨0x5668546DC1BC8189⟩⟩⟩,
    ⟨⟨⟨0x385F308022E74768⟩, ⟨0x813555B112B0FE9C⟩⟩, ⟨⟨0x3B65F1FC3D281B70⟩, ⟨0x930DC8303513FD75⟩⟩⟩,
    ⟨⟨⟨0x9330CE0A8B54D9EF⟩, ⟨0xFA3D2271A9DA8AB8⟩⟩, ⟨⟨0x6FFED1B3C16E1E86⟩, ⟨0x963A0BAC2915A224⟩⟩⟩)]

/-- **The eight `K` products agree with the reference.** -/
theorem mul_kat_K : katK.map (fun t => t.1 * t.2.1) = katK.map (·.2.2) := by decide +kernel

/-- The reference's first product with the trace-zero constant `α = y`. -/
def wrongK : K :=
  ⟨⟨⟨0xDD6B216E8AB5D973⟩, ⟨0xB827A948ADD34C32⟩⟩, ⟨⟨0x423E1CBA3D46D2A5⟩, ⟨0xFBB4F8964518C30E⟩⟩⟩

/-- Negative: the first product is not the one with `α = y`. -/
theorem mul_kat_K_ne : katK[0]!.1 * katK[0]!.2.1 ≠ wrongK := by decide +kernel

/-! ## Inverses, squares, generators -/

/-- The inverse of a random `F` element: `a * a⁻¹ = 1` (one `B64` inversion in the kernel). -/
theorem mul_inv_F : katF[0]!.1 * (katF[0]!.1)⁻¹ = 1 := by decide +kernel

/-- The inverse of a random `K` element. -/
theorem mul_inv_K : katK[0]!.1 * (katK[0]!.1)⁻¹ = 1 := by decide +kernel

/-- Squaring is the product on a random `K` element (the `α`-term of `K.sq`). -/
theorem sq_kat_K : K.sq katK[1]!.1 = katK[1]!.1 * katK[1]!.1 := by decide +kernel

/-- Negative: `y^2 ≠ y + x^61`, i.e. the modulus is not `y^2 + y + x^61` (the other trace-1
monomial, the most plausible wrong `β`). -/
theorem y_sq_ne_x61 : F.y * F.y ≠ F.y + F.ofB64 ⟨0x2000000000000000⟩ := by decide +kernel

/-- `0⁻¹ = 0`. -/
theorem inv_zero_F : (0 : F)⁻¹ = 0 := by decide +kernel

/-- Negative: the inverse without the conjugation, `a · (a / norm a)`, is not `1` on a random
element (the conjugate `(c₀ + c₁) + c₁ y` in `F.inv` matters). -/
theorem inv_no_conj_ne :
    katF[0]!.1 * F.smulBase (F.norm katF[0]!.1)⁻¹ katF[0]!.1 ≠ 1 := by decide +kernel

/-! ## Bytes -/

/-- `F` bytes are `c₀`'s eight little-endian bytes, then `c₁`'s. -/
theorem toBytes_F : (F.toBytes ⟨⟨0x0807060504030201⟩, ⟨0x100F0E0D0C0B0A09⟩⟩).toList =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] := by decide +kernel

/-- Negative: not `c₁` first. -/
theorem toBytes_F_ne : (F.toBytes ⟨⟨0x0807060504030201⟩, ⟨0x100F0E0D0C0B0A09⟩⟩).toList ≠
    [9, 10, 11, 12, 13, 14, 15, 16, 1, 2, 3, 4, 5, 6, 7, 8] := by decide +kernel

/-- `K` bytes are `f₀`'s sixteen bytes, then `f₁`'s. -/
theorem toBytes_K : (K.toBytes ⟨⟨⟨0x0807060504030201⟩, ⟨0x100F0E0D0C0B0A09⟩⟩,
    ⟨⟨0x1817161514131211⟩, ⟨0x201F1E1D1C1B1A19⟩⟩⟩).toList =
    (List.range 32).map (fun i => i.toUInt8 + 1) := by
  decide +kernel

/-! ## The trace hypothesis is needed -/

/-- `ω = x^((2^64 - 1)/3)`, a primitive cube root of unity in `GF(2^64)` (printed by `kat.py`). -/
def omega : B64 := ⟨0x19C9369F278ADC02⟩

/-- `ω` is a root of `y^2 + y + 1`, by kernel evaluation. -/
theorem omega_root : omega * omega + omega + 1 = 0 := by decide +kernel

/-- The constant `1` has absolute trace `0` (`64` is even). -/
theorem absTrace_one : absTrace 64 (1 : BF64) = 0 := by
  simp only [absTrace, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [show ((64 : ℕ) : BF64) = 2 * 32 by norm_num, CharTwo.two_eq_zero, zero_mul]

/-- **Negative control for the trace criterion**: with the trace-zero constant `1`, the quadratic
`y^2 + y + 1` has a root and is reducible over `BF64`. -/
theorem not_irreducible_one : ¬ Irreducible (X ^ 2 + X + C 1 : BF64[X]) := by
  intro h
  have hr : IsRoot (X ^ 2 + X + C 1 : BF64[X]) (B64.toBF64 omega) := by
    have := congrArg B64.toBF64 omega_root
    simp only [B64.toBF64_add, B64.toBF64_mul, B64.toBF64_one, B64.toBF64_zero] at this
    simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C]
    linear_combination this
  have h1 := degree_eq_one_of_irreducible_of_root h hr
  have h2 : (X ^ 2 + X + C 1 : BF64[X]).degree = 2 := by compute_degree!
  rw [h2] at h1
  exact absurd h1 (by decide)

/-- Negative: a modulus with zero constant is reducible (`y = 0` is a root). -/
theorem not_irreducible_zero : ¬ Irreducible (X ^ 2 + X : BF64[X]) := by
  intro h
  have h1 := degree_eq_one_of_irreducible_of_root h (x := 0) (by simp)
  have h2 : (X ^ 2 + X : BF64[X]).degree = 2 := by compute_degree!
  rw [h2] at h1
  exact absurd h1 (by decide)

/-- Positive, for contrast: `y^2 + y + β` is irreducible (`f128_irreducible`), stated on the
polynomial itself. -/
theorem irreducible_beta : Irreducible (X ^ 2 + X + C betaBF : BF64[X]) :=
  f128Params_poly ▸ f128_irreducible

end FR.FieldControls
