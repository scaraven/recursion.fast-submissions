-- lvm6 X1 (BLUEPRINT §3 `FD1`): the pure specification of the quasi-linear one-error Reed–Solomon
-- decoder. New; built on season 1's novel basis and additive NTTs (`LvmXDec`: `bflyRun`, `fwdRun`,
-- `encN`, `ptK`).
import LvmMPXNtt4

/-!
# `FD1`: one-error Reed–Solomon decoding in quasi-linear time (the pure form)

The code is the Reed–Solomon code of messages `c : Fin k → K` in the novel basis on the domain
`V = ptK [0, 2^ℓ)` (`encN ptK c j = Σ_x c_x X_x(ptK j)`, season 1's `Enc`). The decoder is given
a list `S` of `k + 2` positions of `V` and values `y` that agree with `Enc(c)` on `S` except at
most at one position (`OneErr`), and returns `c` (`fd1_correct`, in `Lvm6FDCorrect`).

## Algorithm (BLUEPRINT §3, review RV1 §2)

With `n = 2^ℓ` and `Λ = Π_{j < n, j ∉ S} (X − ptK j)`:

1. **Product tree** (`lam`): leaf `j < n` is `X − ptK j`, or `1` when `j ∈ S` (a dummy leaf);
   a node of height `h` is kept as its values on `ptK [0, 2^(h+1))`, twice its degree bound.
   A level extends both children to `ptK [0, 2^(h+2))` (`ext`: inverse NTT, zero padding, forward
   NTT) and multiplies pointwise (`treeLevel`). The root (`lam N S ℓ`) holds `Λ` on
   `ptK [0, 2n)`, that is on `V` and on the next coset.
2. **Syndromes** `s₀ = Σ_{j ∈ S} y_j Λ(ptK j)`, `s₁ = Σ_{j ∈ S} y_j Λ(ptK j) ptK j` (the dual of a
   generalised RS code on `S` has multipliers `Λ(a)/c_V`). If `s₀ ≠ 0` the error sits at the
   position whose word is `s₁/s₀`; correcting it adds `s₀` to `y Λ` there (`gIn`).
3. **The `f·Λ` step**: `g = f·Λ` has degree `< n` and the values `gIn` on `V`: inverse NTT, zero
   padding, forward NTT gives `g` on `ptK [0, 2n)` (`gEval`); dividing by `Λ` on the coset gives `f`
   there (`fCos`); an inverse NTT of size `2n` whose low half is zero leaves `f`'s coefficients in
   its high half (`fd1`).

Every function below mirrors the extractor program of `Lvm6FDIR` step for step (sums in list
order, the correction guarded by `idx < n`), so that the program's semantics is this function.
-/

namespace Lvm6.FD

open Lvm.Nb Lvm.X Finset

/-- **Leaves** at height 0: node `j` (`X − ptK j`, or `1` for `j ∈ S`) as its values at
`ptK 0 = 0`, `ptK 1 = 1`, in cells `2j`, `2j + 1`. -/
def leafRow (S : List ℕ) (i : ℕ) : BF64 :=
  if i / 2 ∈ S then 1 else ptK (i / 2) + ptK (i % 2)

/-- **Extension** of a row of values on `ptK [0, 2^(h+1))` to `ptK [0, 2^(h+2))`: inverse NTT,
zero padding, forward NTT. -/
def ext (N h : ℕ) (A : ℕ → BF64) : ℕ → BF64 :=
  fwdRun ptK N (h + 2) fun i => if i < 2 ^ (h + 1) then bflyRun ptK N 0 (h + 1) A i else 0

/-- **One tree level** `h → h + 1`: parent `p` (cells `p·2^(h+2) + x`) is the pointwise product
of its two extended children. -/
def treeLevel (N h : ℕ) (T : ℕ → BF64) (i : ℕ) : BF64 :=
  ext N h (fun j => T (i / 2 ^ (h + 2) * 2 ^ (h + 2) + j)) (i % 2 ^ (h + 2)) *
    ext N h (fun j => T (i / 2 ^ (h + 2) * 2 ^ (h + 2) + 2 ^ (h + 1) + j)) (i % 2 ^ (h + 2))

/-- **The product tree** after `h` levels; `lam N S ℓ` holds `Λ` on `ptK [0, 2^(ℓ+1))`. -/
def lam (N : ℕ) (S : List ℕ) : ℕ → ℕ → BF64
  | 0 => leafRow S
  | h + 1 => treeLevel N h (lam N S h)

/-- The syndrome `s₀ = Σ_{j ∈ S} y_j Λ(ptK j)` (list order). -/
def syn0 (N ℓ : ℕ) (S : List ℕ) (y : ℕ → BF64) : BF64 :=
  (S.map fun j => y j * lam N S ℓ j).sum

/-- The syndrome `s₁ = Σ_{j ∈ S} y_j Λ(ptK j) ptK j` (list order). -/
def syn1 (N ℓ : ℕ) (S : List ℕ) (y : ℕ → BF64) : BF64 :=
  (S.map fun j => y j * lam N S ℓ j * ptK j).sum

/-- The located position: the word `s₁ / s₀` read as a natural number. -/
def errIdx (N ℓ : ℕ) (S : List ℕ) (y : ℕ → BF64) : ℕ :=
  (syn1 N ℓ S y * (syn0 N ℓ S y)⁻¹).toBitVec.toNat

/-- Whether the correction applies at position `j`: `s₀ ≠ 0` and `j = s₁/s₀ < n`. -/
def corrAt (N ℓ : ℕ) (S : List ℕ) (y : ℕ → BF64) (j : ℕ) : Prop :=
  syn0 N ℓ S y ≠ 0 ∧ errIdx N ℓ S y < 2 ^ ℓ ∧ errIdx N ℓ S y = j

instance (N ℓ : ℕ) (S : List ℕ) (y : ℕ → BF64) (j : ℕ) : Decidable (corrAt N ℓ S y j) := by
  unfold corrAt; infer_instance

/-- **The values of `f·Λ` on `V`** after the correction: `y_j Λ(ptK j)` on `S`, `0` elsewhere,
plus `s₀` at the located position. -/
def gIn (N ℓ : ℕ) (S : List ℕ) (y : ℕ → BF64) (j : ℕ) : BF64 :=
  (if j ∈ S then y j * lam N S ℓ j else 0) + if corrAt N ℓ S y j then syn0 N ℓ S y else 0

/-- `f·Λ` on `ptK [0, 2^(ℓ+1))`: inverse NTT of `gIn`, zero padding, forward NTT. -/
def gEval (N ℓ : ℕ) (S : List ℕ) (y : ℕ → BF64) : ℕ → BF64 :=
  fwdRun ptK N (ℓ + 1) fun i => if i < 2 ^ ℓ then bflyRun ptK N 0 ℓ (gIn N ℓ S y) i else 0

/-- `f` on the coset `ptK [2^ℓ, 2^(ℓ+1))` (`(f·Λ)/Λ`), and `0` on `V`. -/
def fCos (N ℓ : ℕ) (S : List ℕ) (y : ℕ → BF64) (i : ℕ) : BF64 :=
  if i < 2 ^ ℓ then 0 else gEval N ℓ S y i * (lam N S ℓ i)⁻¹

/-- **`FD1`**: coefficient `x < 2^ℓ` of the decoded message, from the high half of the size-`2^(ℓ+1)`
inverse NTT of `fCos`. -/
def fd1 (N ℓ : ℕ) (S : List ℕ) (y : ℕ → BF64) (x : ℕ) : BF64 :=
  bflyRun ptK N 0 (ℓ + 1) (fCos N ℓ S y) (2 ^ ℓ + x)

/-- **At most one error**: `S` lists `k + 2` distinct positions of `V = ptK [0, 2^ℓ)`, and `y`
agrees with `Enc(c)` on `S` except possibly at one position `e`. -/
def OneErr (ℓ k : ℕ) (S : List ℕ) (y : ℕ → BF64) (c : Fin k → BF64) : Prop :=
  S.Nodup ∧ S.length = k + 2 ∧ (∀ j ∈ S, j < 2 ^ ℓ) ∧
    ∃ e, ∀ j ∈ S, j ≠ e → y j = encN ptK c j

/-- Non-vacuity of `OneErr`: a word with one wrong value (`y 0 = 1`, `Enc(c) = 0`). -/
theorem oneErr_example : OneErr 1 0 [0, 1] (fun j => if j = 0 then 1 else 0) Fin.elim0 := by
  refine ⟨by decide, rfl, by decide, 0, fun j hj hj0 => ?_⟩
  simp [encN, hj0]

end Lvm6.FD
